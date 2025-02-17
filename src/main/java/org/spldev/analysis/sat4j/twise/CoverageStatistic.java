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

/**
 * Holds statistics regarding coverage of a configuration sample.
 *
 * @author Sebastian Krieter
 */
public class CoverageStatistic {

	protected long numberOfValidConditions;
	protected long numberOfInvalidConditions;
	protected long numberOfCoveredConditions;
	protected long numberOfUncoveredConditions;

	protected double[] configScores;

	protected void initScores(int sampleSize) {
		configScores = new double[sampleSize];
	}

	protected void setScore(int index, double score) {
		configScores[index] = score;
	}

	protected void addToScore(int index, double score) {
		configScores[index] += score;
	}

	protected double getScore(int index) {
		return configScores[index];
	}

	public double[] getConfigScores() {
		return configScores;
	}

	protected void setNumberOfValidConditions(long numberOfValidConditions) {
		this.numberOfValidConditions = numberOfValidConditions;
	}

	protected void setNumberOfInvalidConditions(long numberOfInvalidConditions) {
		this.numberOfInvalidConditions = numberOfInvalidConditions;
	}

	protected void setNumberOfCoveredConditions(long numberOfCoveredConditions) {
		this.numberOfCoveredConditions = numberOfCoveredConditions;
	}

	protected void setNumberOfUncoveredConditions(long numberOfUncoveredConditions) {
		this.numberOfUncoveredConditions = numberOfUncoveredConditions;
	}

	protected void incNumberOfValidConditions() {
		numberOfValidConditions++;
	}

	protected void incNumberOfInvalidConditions() {
		numberOfInvalidConditions++;
	}

	protected void incNumberOfCoveredConditions() {
		numberOfCoveredConditions++;
	}

	protected void incNumberOfUncoveredConditions() {
		numberOfUncoveredConditions++;
	}

	public long getNumberOfValidConditions() {
		return numberOfValidConditions;
	}

	public long getNumberOfInvalidConditions() {
		return numberOfInvalidConditions;
	}

	public long getNumberOfCoveredConditions() {
		return numberOfCoveredConditions;
	}

	public long getNumberOfUncoveredConditions() {
		return numberOfUncoveredConditions;
	}

	public double getCoverage() {
		if (numberOfValidConditions != 0) {
			return (double) numberOfCoveredConditions / (double) numberOfValidConditions;
		} else {
			if (numberOfInvalidConditions == 0) {
				return (double) numberOfCoveredConditions / (double) (numberOfCoveredConditions
					+ numberOfUncoveredConditions);
			} else {
				return 1.0;
			}
		}
	}

}
