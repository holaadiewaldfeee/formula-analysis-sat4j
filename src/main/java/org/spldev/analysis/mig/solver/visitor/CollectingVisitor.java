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
package org.spldev.analysis.mig.solver.visitor;

import org.sat4j.core.*;

public class CollectingVisitor implements Visitor<VecInt[]> {
	final VecInt[] literalList = new VecInt[] { new VecInt(), new VecInt() };

	@Override
	public VisitResult visitStrong(int curLiteral) {
		literalList[0].push(curLiteral);
		return VisitResult.Continue;
	}

	@Override
	public VisitResult visitWeak(int curLiteral) {
		literalList[1].push(curLiteral);
		return VisitResult.Continue;
	}

	@Override
	public VecInt[] getResult() {
		return literalList;
	}
}
