/* -----------------------------------------------------------------------------
 * Formula-Analysis-Sat4J Lib - Library to analyze propositional formulas with Sat4J.
 * Copyright (C) 2021-2022  Sebastian Krieter
 * 
 * This file is part of Formula-Analysis-Sat4J Lib.
 * 
 * Formula-Analysis-Sat4J Lib is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License,
 * or (at your option) any later version.
 * 
 * Formula-Analysis-Sat4J Lib is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with Formula-Analysis-Sat4J Lib.  If not, see <https://www.gnu.org/licenses/>.
 * 
 * See <https://github.com/skrieter/formula-analysis-sat4j> for further information.
 * -----------------------------------------------------------------------------
 */
package org.spldev.analysis.sat4j.twise;

import java.nio.file.*;
import java.util.*;
import java.util.stream.*;

import org.sat4j.core.*;
import org.spldev.analysis.mig.io.*;
import org.spldev.analysis.mig.solver.*;
import org.spldev.analysis.sat4j.*;
import org.spldev.analysis.sat4j.solver.*;
import org.spldev.analysis.sat4j.twise.TWiseConfigurationGenerator.*;
import org.spldev.analysis.solver.SatSolver.*;
import org.spldev.clauses.*;
import org.spldev.clauses.LiteralList.Order;
import org.spldev.clauses.solutions.*;
import org.spldev.util.data.*;
import org.spldev.util.io.*;
import org.spldev.util.job.*;
import org.spldev.util.logging.*;

/**
 * Contains several intermediate results and functions for generating a t-wise
 * sample.
 *
 * @author Sebastian Krieter
 */
public class TWiseConfigurationUtil {

	public enum InvalidClausesList {
		None, Create, Use
	}

	public static final int GLOBAL_SOLUTION_LIMIT = 100_000;

	final static Comparator<Pair<LiteralList, TWiseConfiguration>> candidateLengthComparator = new CandidateLengthComparator();

	protected final LiteralList[] solverSolutions = new LiteralList[GLOBAL_SOLUTION_LIMIT];
	protected final HashSet<LiteralList> solutionSet = new HashSet<>();
	protected Random random = new Random(42);

	protected List<LiteralList> randomSample;

	private final List<TWiseConfiguration> incompleteSolutionList = new LinkedList<>();
	private final List<TWiseConfiguration> completeSolutionList = new ArrayList<>();
	private final HashSet<LiteralList> invalidClauses = new HashSet<>();
	private InvalidClausesList invalidClausesList = InvalidClausesList.None;

	protected final CNF cnf;
	protected final Sat4JSolver localSolver;
	protected final boolean hasSolver;

	protected MIG mig;
	protected LiteralList[] strongHull;
	protected LiteralList coreDead;

	protected int maxSampleSize = Integer.MAX_VALUE;

	private Deduce createConfigurationDeduce = Deduce.DP;
	private Deduce extendConfigurationDeduce = Deduce.NONE;

	public TWiseConfigurationUtil(CNF cnf, Sat4JSolver localSolver) {
		this.cnf = cnf;
		this.localSolver = localSolver;
		hasSolver = localSolver != null;

		randomSample = Collections.emptyList();
	}

	public void computeRandomSample(int randomSampleSize) {
		final FastRandomConfigurationGenerator randomGenerator = new FastRandomConfigurationGenerator();
		randomGenerator.setAllowDuplicates(true);
		randomGenerator.setRandom(random);
		randomGenerator.setLimit(randomSampleSize);
		randomSample = Executor.run(randomGenerator::execute, cnf) //
			.map(SolutionList::getSolutions) //
			.orElse(Logger::logProblems);

		for (final LiteralList solution : randomSample) {
			addSolverSolution(solution.getLiterals());
		}
	}

	public void computeMIG(boolean migCheckRedundancy, boolean migDetectStrong) {
		Logger.logDebug("Init graph... ");
		Logger.logDebug("\tCompute graph... ");
		final MIGBuilder migBuilder = new RegularMIGBuilder();
		migBuilder.setCheckRedundancy(migCheckRedundancy);
		migBuilder.setDetectStrong(migDetectStrong);
		mig = Executor.run(migBuilder, cnf).get();
		setupMIG();
	}

	public void computeMIG(Path migPath) {
		Logger.logDebug("Init graph... ");
		Logger.logDebug("\tLoad graph from " + migPath);
		mig = FileHandler.load(migPath, new MIGFormat()).get();
		setupMIG();
	}

	private void setupMIG() {
		strongHull = new LiteralList[mig.getVertices().size()];

		for (final Vertex vertex : mig.getVertices()) {
			strongHull[MIG.getVertexIndex(vertex)] = new LiteralList(
				vertex.getStrongEdges().stream().mapToInt(Vertex::getVar).toArray());
		}
	}

	public LiteralList getDeadCoreFeatures() {
		if (coreDead == null) {
			if (hasMig()) {
				computeDeadCoreFeaturesMig();
			} else {
				computeDeadCoreFeatures();
			}
		}
		return coreDead;
	}

	public LiteralList computeDeadCoreFeaturesMig() {
		if (hasSolver()) {
			coreDead = new LiteralList();
		} else {
			final int[] coreDeadArray = new int[cnf.getVariableMap().size()];
			int index = 0;
			for (final Vertex vertex : mig.getVertices()) {
				if (vertex.isCore()) {
					coreDeadArray[index++] = vertex.getVar();
				}
			}
			coreDead = new LiteralList(Arrays.copyOf(coreDeadArray, index));
			if (!coreDead.isEmpty()) {
				localSolver.getAssumptions().pushAll(coreDead.getLiterals());
			}
		}
		return coreDead;
	}

	public LiteralList computeDeadCoreFeatures() {
		final Sat4JSolver solver = new Sat4JSolver(cnf);
		final int[] firstSolution = solver.findSolution().getLiterals();
		if (firstSolution != null) {
			final int[] coreDeadArray = new int[firstSolution.length];
			int coreDeadIndex = 0;
			solver.setSelectionStrategy(SStrategy.inverse(firstSolution));
			solver.hasSolution();
			LiteralList.resetConflicts(firstSolution, solver.getInternalSolution());

			// find core/dead features
			for (int i = 0; i < firstSolution.length; i++) {
				final int varX = firstSolution[i];
				if (varX != 0) {
					solver.getAssumptions().push(-varX);
					switch (solver.hasSolution()) {
					case FALSE:
						solver.getAssumptions().replaceLast(varX);
						coreDeadArray[coreDeadIndex++] = varX;
						break;
					case TIMEOUT:
						solver.getAssumptions().pop();
						break;
					case TRUE:
						solver.getAssumptions().pop();
						LiteralList.resetConflicts(firstSolution, solver.getInternalSolution());
						solver.shuffleOrder(random);
						break;
					}
				}
			}
			coreDead = new LiteralList(Arrays.copyOf(coreDeadArray, coreDeadIndex));
			if (!coreDead.isEmpty()) {
				localSolver.getAssumptions().pushAll(coreDead.getLiterals());
			}
		} else {
			coreDead = new LiteralList();
		}
		return coreDead;
	}

	public CNF getCnf() {
		return cnf;
	}

	public Sat4JSolver getSolver() {
		return localSolver;
	}

	public MIG getMig() {
		return mig;
	}

	public boolean hasSolver() {
		return hasSolver;
	}

	public boolean hasMig() {
		return mig != null;
	}

	public Random getRandom() {
		return random;
	}

	protected int solverSolutionEndIndex = -1;

	public void addSolverSolution(int[] literals) {
		final LiteralList solution = new LiteralList(literals, Order.INDEX, false);
		if (solutionSet.add(solution)) {
			solverSolutionEndIndex++;
			solverSolutionEndIndex %= GLOBAL_SOLUTION_LIMIT;
			final LiteralList oldSolution = solverSolutions[solverSolutionEndIndex];
			if (oldSolution != null) {
				solutionSet.remove(oldSolution);
			}
			solverSolutions[solverSolutionEndIndex] = solution;

			for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
				configuration.updateSolverSolutions(literals, solverSolutionEndIndex);
			}
		}
	}

	public LiteralList getSolverSolution(int index) {
		return solverSolutions[index];
	}

	public LiteralList[] getSolverSolutions() {
		return solverSolutions;
	}

	public boolean isCombinationValid(LiteralList literals) {
		return !isCombinationInvalidMIG(literals) && isCombinationValidSAT(literals);
	}

	public boolean isCombinationValid(ClauseList clauses) {
		if (hasSolver()) {
			if (invalidClausesList == InvalidClausesList.Use) {
				for (final LiteralList literalSet : clauses) {
					if (invalidClauses.contains(literalSet)) {
						return false;
					}
				}
				return !clauses.isEmpty();
			}
			if (hasMig()) {
				for (final LiteralList literalSet : clauses) {
					if (isCombinationInvalidMIG(literalSet)) {
						if (invalidClausesList == InvalidClausesList.Create) {
							invalidClauses.add(literalSet);
						}
						return false;
					}
				}
			}
			for (final LiteralList literalSet : clauses) {
				if (isCombinationValidSAT(literalSet)) {
					return true;
				} else {
					if (invalidClausesList == InvalidClausesList.Create) {
						invalidClauses.add(literalSet);
					}
				}
			}
			return false;
		}
		return !clauses.isEmpty();
	}

	public boolean isCombinationInvalidMIG(LiteralList literals) {
		if (hasMig()) {
			for (final int literal : literals.getLiterals()) {
				if (strongHull[MIG.getVertexIndex(literal)].hasConflicts(literals)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean isCombinationValidSAT(LiteralList literals) {
		if (hasSolver()) {
			for (final LiteralList s : randomSample) {
				if (!s.hasConflicts(literals)) {
					return true;
				}
			}

			final Sat4JSolver solver = getSolver();
//			solver.setSelectionStrategy(SStrategy.random(getRandom()));
			final int orgAssignmentLength = solver.getAssumptions().size();
			try {
				solver.getAssumptions().pushAll(literals.getLiterals());
				final SatResult hasSolution = solver.hasSolution();
				switch (hasSolution) {
				case TRUE:
					final int[] solution = solver.getInternalSolution();
					addSolverSolution(Arrays.copyOf(solution, solution.length));
					solver.shuffleOrder(random);
					break;
				case FALSE:
				case TIMEOUT:
					return false;
				default:
					break;
				}
			} finally {
				solver.getAssumptions().clear(orgAssignmentLength);
			}
		}
		return true;
	}

	public boolean removeInvalidClauses(ClauseList nextCondition,
		List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralList> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralList> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralList literals = conditionIterator.next();
			if (!isCombinationValid(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	public boolean removeInvalidClausesSat(ClauseList nextCondition,
		List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralList> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralList> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralList literals = conditionIterator.next();
			if (!isCombinationValidSAT(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	public boolean removeInvalidClausesLight(ClauseList nextCondition,
		List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		final LinkedList<LiteralList> invalidClauses = new LinkedList<>();
		for (final Iterator<LiteralList> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralList literals = conditionIterator.next();
			if (isCombinationInvalidMIG(literals)) {
				invalidClauses.add(literals);
				conditionIterator.remove();
			}
		}
		if (nextCondition.isEmpty()) {
			candidatesList.clear();
			return true;
		} else {
			removeInvalidCandidates(candidatesList, invalidClauses);
			return false;
		}
	}

	private void removeInvalidCandidates(List<Pair<LiteralList, TWiseConfiguration>> candidatesList,
		final LinkedList<LiteralList> invalidClauses) {
		for (final LiteralList literals : invalidClauses) {
			for (final Iterator<Pair<LiteralList, TWiseConfiguration>> candidateIterator = candidatesList
				.iterator(); candidateIterator.hasNext();) {
				final Pair<LiteralList, TWiseConfiguration> pair = candidateIterator.next();
				if (pair.getKey().equals(literals)) {
					candidateIterator.remove();
				}
			}
		}
	}

	public boolean removeInvalidClausesLight(ClauseList nextCondition) {
		for (final Iterator<LiteralList> conditionIterator = nextCondition.iterator(); conditionIterator.hasNext();) {
			final LiteralList literals = conditionIterator.next();
			if (isCombinationInvalidMIG(literals)) {
				conditionIterator.remove();
			}
		}
		return nextCondition.isEmpty();
	}

	private boolean isSelectionPossibleSol(Pair<LiteralList, TWiseConfiguration> candidate) {
		final VecInt solverSolutionIndex = candidate.getValue().getSolverSolutionIndex();
		for (int i = 0; i < solverSolutionIndex.size(); i++) {
			if (!getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(candidate.getKey())) {
				return true;
			}
		}
		return false;
	}

	private boolean isSelectionPossibleSol(LiteralList literals, TWiseConfiguration configuration) {
		final VecInt solverSolutionIndex = configuration.getSolverSolutionIndex();
		for (int i = 0; i < solverSolutionIndex.size(); i++) {
			if (!getSolverSolution(solverSolutionIndex.get(i)).hasConflicts(literals)) {
				return true;
			}
		}
		return false;
	}

	private boolean isSelectionPossibleSat(final LiteralList literals, final TWiseConfiguration configuration) {
		if (hasSolver) {
			final Sat4JSolver localSolver = getSolver();
//			localSolver.setSelectionStrategy(SStrategy.random());
			final int orgAssignmentSize = configuration.setUpSolver(localSolver);
			try {
				final int[] configurationLiterals = configuration.getLiterals();
				for (final int literal : literals.getLiterals()) {
					if (configurationLiterals[Math.abs(literal) - 1] == 0) {
						localSolver.getAssumptions().push(literal);
					}
				}
				if (orgAssignmentSize < localSolver.getAssumptions().size()) {
					if (localSolver.hasSolution() == SatResult.TRUE) {
						final int[] solution = localSolver.getInternalSolution();
						addSolverSolution(Arrays.copyOf(solution, solution.length));
						localSolver.shuffleOrder(random);
					} else {
						return false;
					}
				}
			} finally {
				localSolver.getAssumptions().clear(orgAssignmentSize);
			}
		}
		return true;
	}

	public static boolean isCovered(ClauseList condition, Iterable<? extends LiteralList> solutionList) {
		for (final LiteralList configuration : solutionList) {
			for (final LiteralList literals : condition) {
				if (configuration.containsAll(literals)) {
					return true;
				}
			}
		}
		return false;
	}

	private Stream<TWiseConfiguration> getConfigurationStream() {
		return Stream.concat(getCompleteSolutionList().parallelStream(), getIncompleteSolutionList().parallelStream());
	}

	public boolean isCoveredPara(ClauseList condition) {
		final Optional<TWiseConfiguration> coveringSolution = condition.stream() //
			.flatMap(literals -> getConfigurationStream() //
				.filter(configuration -> configuration.containsAll(literals)))//
			.findAny();
		return coveringSolution.isPresent();
	}

	public boolean isCovered(ClauseList condition) {
		return isCovered(condition, completeSolutionList) || isCovered(condition, incompleteSolutionList);
	}

	public boolean select(TWiseConfiguration solution, Deduce deduce, LiteralList literals) {
		selectLiterals(solution, deduce, literals);

		if (solution.isComplete()) {
			solution.clear();
			for (final Iterator<TWiseConfiguration> iterator = incompleteSolutionList.iterator(); iterator.hasNext();) {
				if (iterator.next() == solution) {
					iterator.remove();
					completeSolutionList.add(solution);
					break;
				}
			}
			return true;
		} else {
			return false;
		}
	}

	private void selectLiterals(TWiseConfiguration solution, Deduce deduce, LiteralList literals) {
		solution.setLiteral(literals.getLiterals());
		if (hasSolver()) {
			switch (deduce) {
			case AC:
				solution.autoComplete();
				break;
			case DP:
				solution.propagation();
				break;
			case NONE:
				break;
			}
		}
	}

	public boolean isCandidate(final LiteralList literals, TWiseConfiguration solution) {
		return !solution.hasConflicts(literals);
	}

	public boolean isCandidate(final Pair<LiteralList, TWiseConfiguration> pair) {
		return !pair.getValue().hasConflicts(pair.getKey());
	}

	public void addCandidates(final LiteralList literals, List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
			if (isCandidate(literals, configuration)) {
				candidatesList.add(new Pair<>(literals, configuration));
			}
		}
	}

	public void initCandidatesListPara(ClauseList nextCondition,
		List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		candidatesList.clear();
		nextCondition.stream() //
			.flatMap(literals -> getIncompleteSolutionList().parallelStream() //
				.filter(configuration -> isCandidate(literals, configuration)) //
				.map(configuration -> new Pair<>(literals, configuration)))//
			.sorted(candidateLengthComparator) //
			.forEach(candidatesList::add);
	}

	public void initCandidatesList(ClauseList nextCondition,
		List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		candidatesList.clear();
		for (final LiteralList literals : nextCondition) {
			for (final TWiseConfiguration configuration : getIncompleteSolutionList()) {
				if (isCandidate(literals, configuration)) {
					candidatesList.add(new Pair<>(literals, configuration));
				}
			}
		}
		Collections.sort(candidatesList, candidateLengthComparator);
	}

	protected boolean coverSol(List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralList, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleSol(pair.getKey(), pair.getValue())) {
				assert pair.getValue().isValid();
				select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
				return true;
			}
		}
		return false;
	}

	protected boolean coverSat(List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralList, TWiseConfiguration> pair : candidatesList) {
			if (isSelectionPossibleSat(pair.getKey(), pair.getValue())) {
				select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
				assert pair.getValue().isValid();
				return true;
			}
		}
		return false;
	}

	protected boolean coverNoSat(List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		for (final Pair<LiteralList, TWiseConfiguration> pair : candidatesList) {
			select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
			return true;
		}
		return false;
	}

	protected boolean coverSolPara(List<Pair<LiteralList, TWiseConfiguration>> candidatesList) {
		final Optional<Pair<LiteralList, TWiseConfiguration>> candidate = candidatesList.parallelStream() //
			.filter(this::isSelectionPossibleSol) //
			.findFirst();

		if (candidate.isPresent()) {
			final Pair<LiteralList, TWiseConfiguration> pair = candidate.get();
			select(pair.getValue(), extendConfigurationDeduce, pair.getKey());
			assert pair.getValue().isValid();
			return true;
		} else {
			return false;
		}
	}

	public void newConfiguration(final LiteralList literals) {
		if (completeSolutionList.size() < maxSampleSize) {
			final TWiseConfiguration configuration = new TWiseConfiguration(this);
			selectLiterals(configuration, createConfigurationDeduce, literals);
			assert configuration.isValid();
			configuration.updateSolverSolutions();
			if (configuration.isComplete()) {
				configuration.clear();
				completeSolutionList.add(configuration);
			} else {
				incompleteSolutionList.add(configuration);
				Collections.sort(incompleteSolutionList, (a, b) -> a.countLiterals() - b.countLiterals());
			}
		}
	}

	public List<TWiseConfiguration> getIncompleteSolutionList() {
		return incompleteSolutionList;
	}

	public List<TWiseConfiguration> getCompleteSolutionList() {
		return completeSolutionList;
	}

	public List<TWiseConfiguration> getResultList() {
		final ArrayList<TWiseConfiguration> resultList = new ArrayList<>(
			completeSolutionList.size() + incompleteSolutionList.size());
		resultList.addAll(incompleteSolutionList);
		resultList.addAll(completeSolutionList);
		return resultList;
	}

	public int getMaxSampleSize() {
		return maxSampleSize;
	}

	public void setMaxSampleSize(int maxSampleSize) {
		this.maxSampleSize = maxSampleSize;
	}

	public void setRandom(Random random) {
		this.random = random;
	}

	public void setCreateConfigurationDeduce(Deduce createConfigurationDeduce) {
		this.createConfigurationDeduce = createConfigurationDeduce;
	}

	public void setExtendConfigurationDeduce(Deduce extendConfigurationDeduce) {
		this.extendConfigurationDeduce = extendConfigurationDeduce;
	}

	public void setMIG(MIG mig) {
		this.mig = mig;
		setupMIG();
	}

	public void setInvalidClausesList(InvalidClausesList invalidClausesList) {
		this.invalidClausesList = invalidClausesList;
	}

}
