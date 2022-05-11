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
package org.spldev.assignment;

import java.nio.file.*;
import java.util.*;
import java.util.function.*;
import java.util.stream.*;

import org.spldev.analysis.sat4j.*;
import org.spldev.analysis.sat4j.twise.*;
import org.spldev.clauses.*;
import org.spldev.clauses.LiteralList.*;
import org.spldev.clauses.solutions.*;
import org.spldev.clauses.solutions.analysis.*;
import org.spldev.formula.*;
import org.spldev.formula.structure.atomic.literal.*;
import org.spldev.formula.structure.compound.*;
import org.spldev.formula.structure.term.bool.*;
import org.spldev.util.extension.*;
import org.spldev.util.job.*;
import org.spldev.util.logging.*;

public class InteractionFinderTest {

	static {
		ExtensionLoader.load();
	}

	private static final int maxT = 5;

	private static final Random random = new Random(0);
	private static final int interactionSize = 3;
	private static final int iterations = 100;

	private static final int sampleSize = 10;

	private static class SimpleRandomConfigurationGenerator implements SolutionUpdater {
		private final int configurationSize;

		public SimpleRandomConfigurationGenerator(int configurationSize) {
			this.configurationSize = configurationSize;
		}

		@Override
		public Optional<LiteralList> complete(LiteralList partial) {
			final int[] assignment = new int[configurationSize];
			for (int i = 0; i < assignment.length; i++) {
				assignment[i] = random.nextBoolean() ? (i + 1) : -(i + 1);
			}
			if (partial != null) {
				for (int i = 0; i < partial.size(); i++) {
					int fixedLiteral = partial.get(i);
					assignment[Math.abs(fixedLiteral) - 1] = fixedLiteral;
				}
			}
			return Optional.of(new LiteralList(assignment, Order.INDEX, false));
		}
	}

	private static class ConfigurationVerifier implements Predicate<LiteralList> {
		private final LiteralList interaction;

		public ConfigurationVerifier(LiteralList interaction) {
			this.interaction = interaction;
		}

		@Override
		public boolean test(LiteralList configuration) {
			return !configuration.containsAll(interaction);
		}

	}

	public static void main(String[] args) {
		new InteractionFinderTest().printCompare();
	}

	public void printCompare() {
		int failCount = 0;
		final ModelRepresentation model = getModel(Paths.get("src/test/resources/GPL/model.xml"));
//		final ModelRepresentation model = getModel(numberOfFeatures);
		final LiteralList core = model.get(new CoreDeadAnalysis());
		for (int i = 0; i < iterations; i++) {
			final List<LiteralList> sample = createRandomSample(model, sampleSize);
//			final Collection<LiteralList> sample = createTWiseSample(model, 2);

			ConfigurationVerifier verifier = new ConfigurationVerifier(chooseInteraction(random, sample,
				interactionSize));

//			final InteractionFinder finder = new InteractionFinder(sample,
//				createRandomCompletor(model), verifier);

			final InteractionFinderNaive finder = new InteractionFinderNaive(sample,
				createCompletor(model), verifier);
			finder.setCore(core);

			LiteralList result = finder.find(verifier.interaction.size());
//			LiteralList result = finder.findTWise(verifier.interaction.size());
//			LiteralList result = finder.findInteraction(maxT);

			String message;
			if (verifier.interaction.equals(result)) {
				message = "%d/%d OK   %s > %s";
			} else {
				failCount++;
				message = "%d/%d FAIL %s > %s";
			}
			System.out.println(String.format(message,
				(i + 1),
				iterations,
				str(verifier.interaction),
				str(result)));
		}
		System.out.println("Fails: " + failCount);
	}

	private static String str(LiteralList findTWise) {
		return Arrays.toString(findTWise.getLiterals());
	}

	private static ModelRepresentation getModel(int size) {
		final VariableMap variables = VariableMap.fixedSize(size);
		LiteralPredicate l = new LiteralPredicate((BoolVariable) (variables.getVariable(1).get()), true);
		return new ModelRepresentation(new Or(l, l.flip()), variables);
	}

	private static ModelRepresentation getModel(Path path) {
		return ModelRepresentation.load(path).orElse(Logger::logProblems);
	}

	private static List<LiteralList> createRandomSample(ModelRepresentation rep, int size) {
		RandomConfigurationGenerator generator = new FastRandomConfigurationGenerator();
		generator.setAllowDuplicates(false);
		generator.setRandom(new Random(0));
		generator.setLimit(size);
		return rep.getResult(generator).map(SolutionList::getSolutions).orElse(Logger::logProblems);
	}

	private static List<LiteralList> createTWiseSample(ModelRepresentation rep, int t) {
		TWiseConfigurationGenerator generator = new TWiseConfigurationGenerator();
		generator.setRandom(new Random(0));
		generator.setT(t);
		return rep.getResult(generator).map(SolutionList::getSolutions).orElse(Logger::logProblems);
	}

	public static ConfigurationCompletor createCompletor(ModelRepresentation rep) {
		RandomConfigurationGenerator randomGenerator = new FastRandomConfigurationGenerator();
		randomGenerator.setAllowDuplicates(false);
		randomGenerator.setRandom(new Random(0));
		randomGenerator.init(rep, new NullMonitor());
		return new ConfigurationCompletor(rep, randomGenerator);
	}

	public static SolutionUpdater createRandomCompletor(ModelRepresentation rep) {
		return new SimpleRandomConfigurationGenerator(rep.getVariables().size());
	}

	private static LiteralList chooseInteraction(Random random, List<LiteralList> solutions, int interactionSize) {
		final LiteralList solution = solutions.get(random.nextInt(solutions.size()));
		return new LiteralList(Stream.generate(() -> (random.nextInt(solution.size()))) //
			.mapToInt(Integer::intValue) //
			.distinct() //
			.limit(interactionSize) //
			.map(l -> solution.get(l)) //
			.toArray());
	}

}
