// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.testing

/**
 * A class that holds information about the projects under the test.
 *
 * @param projectNames a list of tested projects
 */
class ProjectInfo(val projectNames: List[String]) {

  /**
   * A string representing all projects being tested.
   */
  val fullName = projectNames.mkString("-")

  /**
   * Create a new ProjectInfo object with a new project added to the list.
   * @param projectName
   * @return
   */
  def update(projectName: String): ProjectInfo = new ProjectInfo(projectName :: projectNames)

}
