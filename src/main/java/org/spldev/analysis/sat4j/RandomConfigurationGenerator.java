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

import org.spldev.analysis.solver.*;
import org.spldev.clauses.*;
import org.spldev.util.job.*;

/**
 * Finds random valid solutions of propositional formulas.
 *
 * @author Sebastian Krieter
 */
public abstract class RandomConfigurationGenerator extends AbstractConfigurationGenerator {

	public RandomConfigurationGenerator() {
		super();
		setRandom(new Random());
	}

	@Override
	protected void init(InternalMonitor monitor) {
		super.init(monitor);
	}

		//HERE
	@Override
	public LiteralList get() {
		reset();
		solver.shuffleOrder(random);
		final LiteralList solution = solver.findSolution();
		if (solution == null) {
			return null;
		}
		if (!allowDuplicates) {
			try {
				forbidSolution(solution.negate());
			} catch (final RuntimeContradictionException e) {
			}
		}
		return solution;
	}

	protected void forbidSolution(final LiteralList negate) {
		solver.getFormula().push(negate);
	}

	protected void reset() {
	}

}
