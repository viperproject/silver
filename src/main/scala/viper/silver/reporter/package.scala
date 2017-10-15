/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver

package object reporter {
  type Time = Long // in milliseconds
  type File = java.nio.file.Path
  type Entity = viper.silver.ast.Member with Serializable
  type Position = viper.silver.ast.SourcePosition
}
