/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.reporter

trait Reporter {
  val name: String

  def report(msg: Message): Unit
}

object NoopReporter extends Reporter {
  val name: String = "NoopReporter"
  def report(msg: Message): Unit = ()
}

class StdIOReporter(val name: String) extends Reporter {
  var counter = 0

  def report(msg: Message): Unit = {
    println(s"$name#$counter: $msg")
    counter = counter + 1
  }
}
