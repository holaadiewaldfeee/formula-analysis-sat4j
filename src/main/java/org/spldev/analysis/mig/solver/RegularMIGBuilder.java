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
package org.spldev.analysis.mig.solver;

import org.spldev.analysis.mig.solver.MIG.*;
import org.spldev.analysis.solver.*;
import org.spldev.clauses.*;
import org.spldev.util.job.*;

/**
 * Adjacency matrix implementation for a feature graph.
 *
 * @author Sebastian Krieter
 */

public class RegularMIGBuilder extends MIGBuilder {

	@Override
	public MIG execute(CNF cnf, InternalMonitor monitor) throws Exception {
		monitor.setTotalWork(24 + (detectStrong ? 1020 : 0) + (checkRedundancy ? 100 : 10));

		init(cnf);
		monitor.step();

		if (!satCheck(cnf)) {
			throw new RuntimeContradictionException("CNF is not satisfiable!");
		}
		monitor.step();
		findCoreFeatures(monitor.subTask(10));

		cleanClauses();
		monitor.step();

		if (detectStrong) {
			addClauses(cnf, false, monitor.subTask(10));

			bfsStrong(monitor.subTask(10));

			bfsWeak(null, monitor.subTask(1000));
			mig.setStrongStatus(BuildStatus.Complete);
		} else {
			mig.setStrongStatus(BuildStatus.None);
		}

		addClauses(cnf, checkRedundancy, monitor.subTask(checkRedundancy ? 100 : 10));

		bfsStrong(monitor.subTask(10));

		finish();
		monitor.step();

		return mig;
	}

}
