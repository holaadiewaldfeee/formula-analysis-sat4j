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
package org.spldev.analysis.mig.io;

import java.util.*;

import org.spldev.analysis.mig.solver.*;
import org.spldev.clauses.*;
import org.spldev.formula.structure.atomic.literal.*;

/**
 * Computes a textual representation of the feature relationships in a modal
 * implication graph.
 *
 * @author Sebastian Krieter
 */
public class MIGDependenciesWriter {

	public String write(final MIG mig, final VariableMap variables) {
		final StringBuilder sb = new StringBuilder();
		sb.append("X ALWAYS Y := If X is selected then Y is selected in every valid configuration.\n");
		sb.append(
			"X MAYBE  Y := If X is selected then Y is selected in at least one but not all valid configurations. \n");
		sb.append("X NEVER  Y := If X is selected then Y cannot be selected in any valid configuration.\n\n");

		final List<Vertex> adjList = mig.getVertices();
		for (final Vertex vertex : adjList) {
			if (!vertex.isCore() && !vertex.isDead()) {
				final int var = vertex.getVar();
				if (var > 0) {
					final String name = variables.getName(var).get();
					for (final Vertex otherVertex : vertex.getStrongEdges()) {
						if (!otherVertex.isCore() && !otherVertex.isDead()) {
							sb.append(name);
							if (otherVertex.getVar() > 0) {
								sb.append(" ALWAYS ");
							} else {
								sb.append(" NEVER ");
							}
							sb.append(variables.getName(otherVertex.getVar()));
							sb.append("\n");
						}
					}
					for (final LiteralList clause : vertex.getComplexClauses()) {
						for (final int otherVar : clause.getLiterals()) {
							if ((otherVar > 0) && (var != otherVar)) {
								sb.append(name);
								sb.append(" MAYBE ");
								sb.append(variables.getName(otherVar));
								sb.append("\n");
							}
						}
					}
				}
			}
		}
		return sb.toString();
	}

}
