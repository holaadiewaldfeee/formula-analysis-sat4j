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
package org.spldev.analysis.sat4j;

import java.util.*;

import org.sat4j.specs.*;
import org.spldev.analysis.sat4j.solver.*;
import org.spldev.analysis.solver.SatSolver.*;
import org.spldev.clauses.*;
import org.spldev.util.data.*;
import org.spldev.util.job.*;

/**
 * Finds redundant clauses with respect to a given {@link CNF}. This analysis
 * works by adding every clause group (see {@link AClauseAnalysis}) to the given
 * {@link CNF} at the beginning an then removing and re-adding each clause group
 * individually. If a clause group is redundant with respect to the current
 * formula, it is marked as redundant and removed completely from the
 * {@link CNF}, otherwise it is kept as part of the {@link CNF} for the
 * remaining analysis. Clauses are added in the same order a they appear in the
 * given clauses list.<br>
 * For an independent analysis of every clause group use
 * {@link IndependentRedundancyAnalysis}.
 *
 * @author Sebastian Krieter
 *
 * @see AddRedundancyAnalysis
 * @see IndependentRedundancyAnalysis
 */
public class RemoveRedundancyAnalysis extends AClauseAnalysis<List<LiteralList>> {

	public static final Identifier<List<LiteralList>> identifier = new Identifier<>();

	@Override
	public Identifier<List<LiteralList>> getIdentifier() {
		return identifier;
	}

	public RemoveRedundancyAnalysis() {
		super();
	}

	public RemoveRedundancyAnalysis(List<LiteralList> clauseList) {
		this.clauseList = clauseList;
	}

	@Override
	public List<LiteralList> analyze(Sat4JSolver solver, InternalMonitor monitor) throws Exception {
		if (clauseList == null) {
			return Collections.emptyList();
		}
		if (clauseGroupSize == null) {
			clauseGroupSize = new int[clauseList.size()];
			Arrays.fill(clauseGroupSize, 1);
		}
		monitor.setTotalWork(clauseGroupSize.length + 1);

		final List<LiteralList> resultList = new ArrayList<>(clauseGroupSize.length);
		for (int i = 0; i < clauseList.size(); i++) {
			resultList.add(null);
		}

		final List<IConstr> constrs = new ArrayList<>(clauseList.size());
		for (final LiteralList clause : clauseList) {
			constrs.add(solver.getFormula().push(clause));
		}

		monitor.step();

		int endIndex = 0;
		for (int i = 0; i < clauseGroupSize.length; i++) {
			final int startIndex = endIndex;
			endIndex += clauseGroupSize[i];
			boolean completelyRedundant = true;
			boolean removedAtLeastOne = false;
			for (int j = startIndex; j < endIndex; j++) {
				final IConstr cm = constrs.get(j);
				if (cm != null) {
					removedAtLeastOne = true;
					solver.getFormula().remove(cm);
				}
			}

			if (removedAtLeastOne) {
				for (int j = startIndex; j < endIndex; j++) {
					final LiteralList clause = clauseList.get(j);

					final SatResult hasSolution = solver.hasSolution(clause.negate());
					switch (hasSolution) {
					case FALSE:
						break;
					case TIMEOUT:
						reportTimeout();
						break;
					case TRUE:
						solver.getFormula().push(clause);
						completelyRedundant = false;
						break;
					default:
						throw new AssertionError(hasSolution);
					}
				}
			}

			if (completelyRedundant) {
				resultList.set(i, clauseList.get(startIndex));
			}
			monitor.step();
		}

		return resultList;
	}

}
