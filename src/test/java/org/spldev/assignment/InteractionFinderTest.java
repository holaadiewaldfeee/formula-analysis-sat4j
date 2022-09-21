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
import java.io.*;
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
import org.spldev.formula.structure.AuxiliaryRoot;
import org.spldev.formula.structure.Expression;
import org.spldev.formula.structure.Formula;
import org.spldev.formula.structure.atomic.Atomic;
import org.spldev.formula.structure.atomic.literal.*;
import org.spldev.formula.structure.compound.*;
import org.spldev.formula.structure.term.Variable;
import org.spldev.formula.structure.term.bool.*;
import org.spldev.util.extension.*;
import org.spldev.util.io.csv.CSVWriter;
import org.spldev.util.job.*;
import org.spldev.util.logging.*;
import org.spldev.util.tree.Trees;
import org.spldev.util.tree.visitor.TreePrinter;
import org.spldev.util.tree.visitor.TreeVisitor;
import org.spldev.util.tree.visitor.TreeVisitor.VisitorResult;

public class InteractionFinderTest {

	static {
		ExtensionLoader.load();
	}

	private static final int maxT = 4;

	private static final Random randomSeed = new Random(314159);
	private static final int interactionSize = 2;
	private static final int iterations = 1;

	private static final int sampleSize = 2;

	private static CSVWriter writer;

	private static class ConfigurationVerifier implements Predicate<LiteralList> {
		private final LiteralList interaction;

		public ConfigurationVerifier(LiteralList interaction) {
			this.interaction = interaction;
		}

		// HERE get true if configuration not contains failing interaction (if
		// configuration is valid)
		@Override
		public boolean test(LiteralList configuration) {
			return !configuration.containsAll(interaction);
		}

	}

	public static void main(String[] args) throws IOException {
//		String s = System.getProperty("user.home");
//		Path path = Paths.get(s, "Desktop/daten.csv");

		writer = new CSVWriter();
		writer.setOutputFile(Paths.get(System.getProperty("user.home"), "Desktop/daten.csv"));
		writer.setHeader("Model", "testi", "testn", "testRes", "failingInteraction", "foundInteraction", "FIListLength",
				"configCount", "interactionCount", "time");

		InteractionFinderTest.printCompare();

//		try (BufferedWriter writeBuf = Files.newBufferedWriter(path)) {
//			writeBuf.write(String.format(
//					"testi;testn;testRes;failingInteraction;foundInteraction;FIListLength;configCount;time;%n"));
//			for (int i = 0; i < results.length; i++) {
//				String line = results[i];
//				writeBuf.write(line);
//			}
//			writeBuf.close();
//		} catch (IOException e) {
//			System.out.printf("IO: %s%n", e.getMessage());
//		}

	}

	private static class AtomicSetReplacer implements TreeVisitor<Void, Expression> {
		final VariableMap variables;
		final List<LiteralList> atomicSets;

		public AtomicSetReplacer(VariableMap variables, List<LiteralList> atomicSets) {
			this.variables = variables;
			this.atomicSets = atomicSets;
		}

		@Override
		public VisitorResult firstVisit(List<Expression> path) {
			final Expression node = TreeVisitor.getCurrentNode(path);
			if (node instanceof Atomic) {
				return VisitorResult.SkipChildren;
			} else if ((node instanceof AuxiliaryRoot) || (node instanceof Compound)) {
				return VisitorResult.Continue;
			} else {
				return VisitorResult.Fail;
			}
		}

		@Override
		public VisitorResult lastVisit(List<Expression> path) {
			final Expression node = TreeVisitor.getCurrentNode(path);
			node.mapChildren(c -> {
				if (c instanceof LiteralPredicate) {
					LiteralPredicate l = (LiteralPredicate) c;
					int index = l.getIndex();
					for (LiteralList atomicSet : atomicSets) {
						if (atomicSet.containsAnyLiteral(index)) {
							int substitute = atomicSet.get(0);
							if (index != substitute) {
								if (l.isPositive()) {
									return new LiteralPredicate(
											(BoolVariable) variables.getVariable(Math.abs(substitute)).get(),
											substitute > 0);
								} else {
									return new LiteralPredicate(
											(BoolVariable) variables.getVariable(Math.abs(substitute)).get(),
											substitute < 0);
								}
							}
							break;
						} else if (atomicSet.containsAnyLiteral(-index)) {
							int substitute = atomicSet.get(0);
							if (-index != substitute) {
								if (l.isPositive()) {
									return new LiteralPredicate(
											(BoolVariable) variables.getVariable(Math.abs(substitute)).get(),
											substitute < 0);
								} else {
									return new LiteralPredicate(
											(BoolVariable) variables.getVariable(Math.abs(substitute)).get(),
											substitute > 0);
								}
							}
							break;
						}
					}
				}
				return null;
			});
			return VisitorResult.Continue;
		}

	}

	public static void printCompare() throws IOException {
//		String[] results = new String[iterations];
		int failCount = 0;

		ArrayList<String> models = new ArrayList<>();
		models.add("src/test/resources/GPL/model.xml");
		models.add("src/test/resources/testFeatureModels/breakfast.xml");
//		models.add("src/test/resources/testFeatureModels/busybox.xml");

		for (String modelName : models) {

			long startTimeLoadModel = System.nanoTime();
//
			ModelRepresentation model = getModel(Paths.get(modelName)); // modeltest.xml
//		ModelRepresentation model = getModel(Paths.get("src/test/resources/testFeatureModels/busybox.xml")); // modeltest.xml
//		ModelRepresentation model = getModel(100);

//		System.out.println(model.getFormula().toString());
			VariableMap variables = model.getVariables().clone();
			System.out.println(variables.toString());

			final List<LiteralList> atomicSets = model.get(new AtomicSetAnalysis());
			LiteralList coreDead = atomicSets.get(0);
			List<LiteralList> atomicSetsWithoutCore = atomicSets.subList(1, atomicSets.size());
			System.out.println("atomic sets: " + atomicSets);

			Formula formulaWithoutAtomicSets = Trees.cloneTree(model.getFormula());
			Trees.traverse(formulaWithoutAtomicSets, new AtomicSetReplacer(variables, atomicSetsWithoutCore));

			VariableMap variablesWithoutAtomicSets = variables.clone();
			for (LiteralList atomicSet : atomicSetsWithoutCore) {
				for (int i = 1; i < atomicSet.getLiterals().length; i++) {
					variablesWithoutAtomicSets.removeIndex(Math.abs(atomicSet.get(i)));
				}
			}
			variablesWithoutAtomicSets = variablesWithoutAtomicSets.normalize();

			formulaWithoutAtomicSets.adaptVariableMap(variablesWithoutAtomicSets);

			coreDead = Clauses.adapt(coreDead, variables, variablesWithoutAtomicSets).get();
			model = new ModelRepresentation(formulaWithoutAtomicSets);
			variables = variablesWithoutAtomicSets;

			System.out.println(variablesWithoutAtomicSets.toString());
			System.out.println(Trees.traverse(formulaWithoutAtomicSets, new TreePrinter()));

			// System.out.println("core/dead: " + coreDead.size());// .size()

			long nextLong = randomSeed.nextLong();

			for (int i = 0; i < iterations; i++) {

				long startIterationTime = System.nanoTime();

				Random sampleRandom = new Random(i + nextLong);

				// HERE add failingConfig
				final List<LiteralList> input = generateInput(model, interactionSize, coreDead, sampleRandom);
				LiteralList failInteraction = input.get(0);
				List<LiteralList> sample = input.subList(1, 3);
//			final List<LiteralList> sample = createRandomSample(model, 1, sampleRandom); //createTWiseSample(model, 2);

				Random completorRandom = new Random(i + nextLong);

				// HERE verifier contains failing interaction
				ConfigurationVerifier verifier = new ConfigurationVerifier(failInteraction);

				final AbstractInteractionFinder finder = new InteractionFinderNaive(sample,
						createCompletor(model, completorRandom), verifier);

				finder.setCore(coreDead);

//			System.out.println(model.getVariables().toString());
//			System.out.println("core/dead: " + coreDead);// .size()

				int numberOfFeats = variables.size();

				List<LiteralList> foundInteraction = finder.find(verifier.interaction.size(),
						numberOfFeats - coreDead.size());

				int foundInteractionListLength = foundInteraction.size();
				System.out.println("ListLength: " + foundInteractionListLength);

				int configurationCount = finder.getConfigurationCount() - sample.size();
				System.out.println("#configs: " + configurationCount);

				long finishIterationTime = System.nanoTime();
				long timeElapsedIteration = finishIterationTime - startIterationTime;
				double elapsedTimeInSecondIteration = (timeElapsedIteration / 1_000_000) / 1_000.0;
//			System.out.println("Time: " + timeElapsedIteration);

//			String message;
//			if (foundInteraction.contains(failInteraction)) { // failInteraction.equals(foundInteraction)
//				message = "%d/%d %s   %s > %s %n";
//			} else {
//				failCount++;
//				message = "%d/%d FAIL %s > %s %n";
//			}

				System.out.println(String.format("%d/%d %s   %s > %s %n", (i + 1), iterations,
						foundInteraction.contains(failInteraction) ? "OK" : "FAIL", str(verifier.interaction),
						str(foundInteraction)));

				writer.createNewLine();
				writer.addValue(modelName);
				writer.addValue((i + 1));
				writer.addValue(iterations);
				writer.addValue(foundInteraction.contains(failInteraction) ? "OK" : "FAIL");
				writer.addValue(str(verifier.interaction));
				writer.addValue(str(foundInteraction));
				writer.addValue(foundInteractionListLength);
				writer.addValue(configurationCount);
				writer.addValue(toStr(finder.getInteractionCounter()));
				writer.addValue(elapsedTimeInSecondIteration);
				writer.flush();
//			String message = "%d;%d;%s;%s;%s;%s;%s;%f;%n";
//			results[i] = String.format(message, //
//					(i + 1), //
//					iterations, //
//					foundInteraction.contains(failInteraction) ? "OK" : "FAIL", //
//					str(verifier.interaction), //
//					str(foundInteraction), //
//					foundInteractionListLength, //
//					configurationCount, //
//					elapsedTimeInSecondIteration);
			}
			System.out.println("Fails: " + failCount);

			long finishTime = System.nanoTime();
			long timeElapsed = finishTime - startTimeLoadModel;
			System.out.println("Time: " + timeElapsed);
			double elapsedTimeInSecond = (timeElapsed / 1_000_000) / 1_000.0;
			System.out.println(elapsedTimeInSecond + " seconds");
		}
	}

	private static String str(LiteralList findTWise) {
		return Arrays.toString(findTWise.getLiterals());
	}

	private static String str(List<LiteralList> findTWise) {
		StringBuilder sb = new StringBuilder();
		findTWise.forEach(list -> sb.append(str(list)));
		return sb.toString();
	}

	private static String toStr(List<?> list) {
		StringBuilder sb = new StringBuilder();
		for (Object object : list) {
			sb.append(String.valueOf(object));
			sb.append(",");
		}
		return sb.toString();
	}

	private static ModelRepresentation getModel(int size) {
		final VariableMap variables = VariableMap.fixedSize(size);
		LiteralPredicate l = new LiteralPredicate((BoolVariable) (variables.getVariable(1).get()), true);
		return new ModelRepresentation(new Or(l, l.flip()), variables);
	}

	private static ModelRepresentation getModel(Path path) {
		return ModelRepresentation.load(path).orElse(Logger::logProblems);
	}

	public static ConfigurationCompletor createCompletor(ModelRepresentation rep, Random random) {
		RandomConfigurationGenerator randomGenerator = new FastRandomConfigurationGenerator();
		randomGenerator.setAllowDuplicates(false);
		randomGenerator.setRandom(random);
		randomGenerator.init(rep, new NullMonitor());
		return new ConfigurationCompletor(rep, randomGenerator);
	}

	private static List<LiteralList> generateInput(ModelRepresentation rep, int interactionSize, LiteralList coreDead,
			Random random) {
		LiteralList solution1 = rep.getResult(getConfigGenerator(random)).map(SolutionList::getSolutions)
				.map(list -> list.get(0)).orElse(Logger::logProblems);
		if (solution1 != null) {
			LiteralList interaction = new LiteralList(Stream.generate(() -> (random.nextInt(solution1.size()) + 1)) //
					.mapToInt(Integer::intValue) //
					.filter(l -> !coreDead.containsAnyVariable(l)).distinct() //
					.limit(interactionSize) //
					.map(l -> solution1.get(l - 1)) //
					.toArray());

			CNF cnf = rep.get(CNFProvider.fromFormula());
			ClauseList clauses = new ClauseList(cnf.getClauses());
			clauses.add(interaction.negate());
			LiteralList solution2 = getConfigGenerator(random)
					.execute(new CNF(cnf.getVariableMap(), clauses), new NullMonitor()).getSolutions().get(0);

			return Arrays.asList(interaction, solution1, solution2);
		}
		throw new RuntimeException();
	}

	private static RandomConfigurationGenerator getConfigGenerator(Random random) {
		RandomConfigurationGenerator generator;
		generator = new FastRandomConfigurationGenerator();
		generator.setAllowDuplicates(false);
		generator.setRandom(random);
		generator.setLimit(1);
		return generator;
	}

//	private static LiteralList chooseInteraction(Random random, List<LiteralList> sample, int interactionSize,
//			LiteralList coreDead) {
//		final LiteralList solution = sample.get(random.nextInt(sample.size()));
//
//		return new LiteralList(Stream.generate(() -> (random.nextInt(solution.size()))) //
//				.mapToInt(Integer::intValue) //
//				.distinct() //
//				.limit(interactionSize) //
//				.map(l -> solution.get(l)) //
//				.toArray());
//	}

//	public static SolutionUpdater createRandomCompletor(ModelRepresentation rep) {
//	return new SimpleRandomConfigurationGenerator(rep.getVariables().size());
//}

//	private static List<LiteralList> createRandomSample(ModelRepresentation rep, int size) {
//	return createRandomSample(rep, size, new Random(0));
//}

//private static List<LiteralList> createRandomSample(ModelRepresentation rep, int size, Random random) {
//	RandomConfigurationGenerator generator = new FastRandomConfigurationGenerator();
//	generator.setAllowDuplicates(false);
//	generator.setRandom(random);
//	generator.setLimit(size);
//	return rep.getResult(generator).map(SolutionList::getSolutions).orElse(Logger::logProblems);
//}

//private static List<LiteralList> createTWiseSample(ModelRepresentation rep, int t) {
//	TWiseConfigurationGenerator generator = new TWiseConfigurationGenerator();
//	generator.setRandom(new Random(0));
//	generator.setT(t);
//	return rep.getResult(generator).map(SolutionList::getSolutions).orElse(Logger::logProblems);
//}

//	private static class SimpleRandomConfigurationGenerator implements SolutionUpdater {
//	private final int configurationSize;
//	private Random random;
//
//	public SimpleRandomConfigurationGenerator(int configurationSize, Random random) {
//		this.configurationSize = configurationSize;
//		this.random = random;
//	}
//
//	@Override
//	public Optional<LiteralList> complete(LiteralList partial) {
//		final int[] assignment = new int[configurationSize];
//		for (int i = 0; i < assignment.length; i++) {
//			assignment[i] = random.nextBoolean() ? (i + 1) : -(i + 1);
//		}
//		if (partial != null) {
//			for (int i = 0; i < partial.size(); i++) {
//				int fixedLiteral = partial.get(i);
//				assignment[Math.abs(fixedLiteral) - 1] = fixedLiteral;
//			}
//		}
//		return Optional.of(new LiteralList(assignment, Order.INDEX, false));
//	}
//}

}
