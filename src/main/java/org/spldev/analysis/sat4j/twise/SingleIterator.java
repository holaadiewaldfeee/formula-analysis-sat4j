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

import java.util.*;

import org.spldev.clauses.*;

/**
 * Uses a {@link RandomPartitionSupplier} to construct a combined presence
 * condition for every combination.
 *
 * @author Sebastian Krieter
 */
public class SingleIterator implements ICombinationSupplier<ClauseList> {

	private final List<PresenceCondition> expressionSet;
	private final ICombinationSupplier<int[]> supplier;
	private final long numberOfCombinations;

	private final TWiseCombiner combiner;
	private final PresenceCondition[] nextCombination;

	public SingleIterator(int t, int n, List<PresenceCondition> expressionSet) {
		this.expressionSet = expressionSet;

		combiner = new TWiseCombiner(n);
		nextCombination = new PresenceCondition[t];

		supplier = new RandomPartitionSupplier(t, expressionSet.size());
		numberOfCombinations = supplier.size();
	}

	@Override
	public ClauseList get() {
		final int[] js = supplier.get();
		if (js != null) {
			for (int j = 0; j < js.length; j++) {
				nextCombination[j] = expressionSet.get(js[j]);
			}
			final ClauseList combinedCondition = new ClauseList();
			combiner.combineConditions(nextCombination, combinedCondition);
			return combinedCondition;
		} else {
			return null;
		}
	}

	@Override
	public long size() {
		return numberOfCombinations;
	}

}
