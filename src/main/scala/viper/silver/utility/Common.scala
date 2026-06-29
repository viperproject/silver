// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import java.io.{
  File => JFile,
  PrintWriter => JPrintWriter,
  BufferedWriter => JBufferedWriter,
  FileWriter => JFileWriter}

/** Utilities that are not tied to Silver itself.
  *
  * TODO: Move into a 'common' sub-project inside Silver (similar to Silicon's
  *       'common' sub-project). If done, consider introducing sub-packages,
  *       for example, 'io'.
  */
object Common {

  /* Utilities simplifying using Scala */

  trait StructuralEquality { self: AnyRef =>
    protected val equalityDefiningMembers: Seq[Any]

    override val hashCode = generateHashCode(equalityDefiningMembers)

    override def equals(other: Any) = (
         this.eq(other.asInstanceOf[AnyRef])
      || (other match {
            case se: StructuralEquality if this.getClass.eq(se.getClass) =>
              equalityDefiningMembers == se.equalityDefiningMembers
            case _ => false
          }))
  }

  /* Take from scala -print when working with case classes. */
  @inline
  def generateHashCode(xs: Any*) = {
    var code = 0

    for (x <- xs)
      code = code * 41 + (if (x == null) 0 else x.##)

    code
  }

  /* Utilities related to I/O */

  /**
   * Writes the `contents` to the given `file`. Existing content will be overwritten.
   *
   * @param contents The content to write.
   * @param file The file to which the content will be written.
   */
  def toFile(contents: String, file: JFile): Unit = {
    val sink = PrintWriter(file)

    sink.write(contents)
    sink.close()
  }

  /** Creates a `java.io.PrintWriter` with `autoFlush` enabled that writes to the given `file`.
    * `File.mkdirs()` is called to ensure that the file path exists.
    *
    * @param file Is assumed to denote a file, not a directory.
    * @param autoFlush Passed on to Java's `PrintWriter`.
    * @param append Passed on to Java's `FileWriter`.
    * @return The instantiated sink.
    */
  def PrintWriter(file: JFile, autoFlush: Boolean = true, append: Boolean = false): JPrintWriter = {
    val pf = file.getParentFile
    if (pf != null) pf.mkdirs()

    new JPrintWriter(new JBufferedWriter(new JFileWriter(file, append)), autoFlush)
  }

  final class Rational(n: BigInt, d: BigInt) extends Ordered[Rational] {
    require(d != 0, "Denominator of Rational must not be 0.")

    private val g = n.gcd(d)
    val numerator: BigInt = n / g * d.signum
    val denominator: BigInt = d.abs / g

    def +(that: Rational): Rational = {
      val newNum = this.numerator * that.denominator + that.numerator * this.denominator
      val newDen = this.denominator * that.denominator
      Rational(newNum, newDen)
    }

    def -(that: Rational): Rational = this + (-that)

    def unary_- = Rational(-numerator, denominator)

    def abs = Rational(numerator.abs, denominator)

    def signum = Rational(numerator.signum, 1)

    def *(that: Rational): Rational = Rational(this.numerator * that.numerator, this.denominator * that.denominator)

    def /(that: Rational): Rational = this * that.inverse

    def inverse = Rational(denominator, numerator)

    def compare(that: Rational) = (this.numerator * that.denominator - that.numerator * this.denominator).signum

    override def equals(obj: Any) = obj match {
      case that: Rational => this.numerator == that.numerator && this.denominator == that.denominator
      case _ => false
    }

    override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(n, d)

    override lazy val toString = s"$numerator/$denominator"
  }

  object Rational extends ((BigInt, BigInt) => Rational) {
    val zero = Rational(0, 1)
    val one = Rational(1, 1)

    def apply(numer: BigInt, denom: BigInt) = new Rational(numer, denom)

    def unapply(r: Rational) = Some(r.numerator, r.denominator)
  }
}
