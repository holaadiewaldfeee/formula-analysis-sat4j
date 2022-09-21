package org.spldev.analysis.sat4j;

import java.util.List;
import java.util.Optional;

import org.spldev.clauses.Clauses;
import org.spldev.clauses.LiteralList;
import org.spldev.clauses.solutions.analysis.SolutionUpdater;
import org.spldev.formula.ModelRepresentation;
import org.spldev.formula.structure.Formula;
import org.spldev.formula.structure.atomic.Assignment;
import org.spldev.formula.structure.atomic.literal.VariableMap;
import org.spldev.util.data.Pair;

public class ConfigurationCompletor implements SolutionUpdater {
	private final ConfigurationGenerator generator;
	private final ModelRepresentation model;

	public ConfigurationCompletor(ModelRepresentation model, ConfigurationGenerator generator) {
		this.generator = generator;
		this.model = model;
	}

	@Override
	public LiteralList update(LiteralList partialSolution) {
		final CoreDeadAnalysis analysis = new CoreDeadAnalysis();
		for (int literal : partialSolution.getLiterals()) {
			analysis.getAssumptions().set(Math.abs(literal), literal > 0);
		}
		return partialSolution.addAll(model.get(analysis));
	}

	@Override
	public Optional<LiteralList> complete(LiteralList partialSolution) {
		final LiteralList result;
		if (partialSolution == null) {
			result = generator.get();
		} else {
			final Assignment assumptions = generator.getAssumptions();
			final List<Pair<Integer, Object>> oldAssumptions = assumptions.getAll();

			for (int literal : partialSolution.getLiterals()) {
				assumptions.set(Math.abs(literal), literal > 0);
			}
			generator.updateAssumptions();

			result = generator.get();

			generator.resetAssumptions();
			assumptions.unsetAll();
			assumptions.setAll(oldAssumptions);
			generator.updateAssumptions();
		}
		return Optional.ofNullable(result);
	}
	
	@Override
	public Optional<LiteralList> complete(LiteralList partialSolution, List<LiteralList> excludeClauses) {
		final LiteralList result;
		if (partialSolution == null) {
			result = generator.get();
		} else {
			final Assignment assumptions = generator.getAssumptions();
			final List<Pair<Integer, Object>> oldAssumptions = assumptions.getAll();

			for (int literal : partialSolution.getLiterals()) {
				assumptions.set(Math.abs(literal), literal > 0);
			}
			VariableMap variables = model.getVariables();
			List<Formula> assumedConstraints = generator.getAssumedConstraints();
			for (LiteralList clause : excludeClauses) {
				assumedConstraints.add(Clauses.toOrClause(clause.negate(), variables));
			}	
			generator.updateAssumptions();

			result = generator.get();

			generator.resetAssumptions();
			assumptions.unsetAll();
			assumptions.setAll(oldAssumptions);
			assumedConstraints.clear();
			generator.updateAssumptions();
		}
		return Optional.ofNullable(result);
	}

}
