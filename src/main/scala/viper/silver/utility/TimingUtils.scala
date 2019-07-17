// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

trait TimingUtils {

  /** Formats a time in milliseconds with fixed column width. */
  def formatTimeForTable(millis: Long): String = {
    if (millis > 1000) "%6.2f sec ".format(millis * 1.0 / 1000)
    else "%6s msec".format(millis.toString)
  }

  /** Formats a time in milliseconds. */
  def formatTime(millis: Long): String = {
    if (millis > 1000) "%.2f sec".format(millis * 1.0 / 1000)
    else "%s msec".format(millis.toString)
  }

  /**
    * Measures the time it takes to execute `f` and returns the result of `f`
    * as well as the required time.
    */
  def time[T](f: () => T): (T, Long) = {
    val start = System.currentTimeMillis()
    val r = f.apply()

    (r, System.currentTimeMillis() - start)
  }
}
