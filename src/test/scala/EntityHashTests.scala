// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

import org.scalatest.matchers.should.Matchers
import org.scalatest.funsuite.AnyFunSuite
import viper.silver.ast._
import viper.silver.utility.CacheHelper

class EntityHashTests extends AnyFunSuite with Matchers {

  val test_prefix = s"Test Entity Hash"

  val domainName: String = "SomeDomain"
  val f0: DomainFunc = DomainFunc("f0", Seq(), Int)(domainName = domainName)
  val f1: DomainFunc = DomainFunc("f1", Seq(), Int)(domainName = domainName)
  val ax0: DomainAxiom = AnonymousDomainAxiom(TrueLit()())(domainName = domainName)
  val ax1: DomainAxiom = AnonymousDomainAxiom(TrueLit()())(domainName = domainName)
  val ax2: DomainAxiom = NamedDomainAxiom("ax2", TrueLit()())(domainName = domainName)
  val ax3: DomainAxiom = NamedDomainAxiom("ax3", TrueLit()())(domainName = domainName)

  private def sameHash(d0: Domain, d1: Domain): Unit = {
    val d0Hash = CacheHelper.computeEntityHash("", d0)
    val d1Hash = CacheHelper.computeEntityHash("", d1)
    d0Hash should be (d1Hash)
  }

  test(s"$test_prefix: domain hash does not depend on order of domain functions") {
    val d0: Domain = Domain(domainName, Seq(f0, f1), Seq(), Seq())()
    val d1: Domain = Domain(domainName, Seq(f1, f0), Seq(), Seq())()
    sameHash(d0, d1)
  }

  test(s"$test_prefix: domain hash does not depend on order of unnamed axioms") {
    val d0: Domain = Domain(domainName, Seq(), Seq(ax0, ax1), Seq())()
    val d1: Domain = Domain(domainName, Seq(), Seq(ax1, ax0), Seq())()
    sameHash(d0, d1)
  }

  test(s"$test_prefix: domain hash does not depend on order of named axioms") {
    val d0: Domain = Domain(domainName, Seq(), Seq(ax2, ax3), Seq())()
    val d1: Domain = Domain(domainName, Seq(), Seq(ax3, ax2), Seq())()
    sameHash(d0, d1)
  }

  test(s"$test_prefix: domain hash does not depend on order of named and unnamed axioms") {
    val d0: Domain = Domain(domainName, Seq(), Seq(ax0, ax1, ax2, ax3), Seq())()
    val d1: Domain = Domain(domainName, Seq(), Seq(ax3, ax1, ax2, ax1), Seq())()
    sameHash(d0, d1)
  }

  test(s"$test_prefix: domain hash does not depend on order of domain functions and named and unnamed axioms") {
    val d0: Domain = Domain(domainName, Seq(f0, f1), Seq(ax0, ax1, ax2, ax3), Seq())()
    val d1: Domain = Domain(domainName, Seq(f1, f0), Seq(ax3, ax1, ax2, ax1), Seq())()
    sameHash(d0, d1)
  }
}
