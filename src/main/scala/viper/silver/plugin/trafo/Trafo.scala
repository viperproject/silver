// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo

import viper.silver.ast._
import viper.silver.verifier.AbstractError
import viper.silver.plugin.trafo.util._

class Trafo(override val program: Program,
            override val reportError: AbstractError => Unit)
  extends ProgramManager