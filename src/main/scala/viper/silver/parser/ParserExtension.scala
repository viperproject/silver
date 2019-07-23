// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import fastparse.noApi
import viper.silver.parser.FastParser._
import viper.silver.plugin._
import scala.collection.Set

object ParserExtension extends ParserPluginTemplate {
  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  import White._
  import fastparse.noApi._

  /**
    * These private variables are the storage variables for each of the extensions.
    * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
    * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
    * can be referenced back.
    */
  private var _newDeclAtEnd: Option[noApi.P[PExtender]] = None
  private var _newDeclAtStart: Option[noApi.P[PExtender]] = None

  private var _newExpAtEnd: Option[noApi.P[PExp]] = None
  private var _newExpAtStart: Option[noApi.P[PExp]] = None

  private var _newStmtAtEnd: Option[noApi.P[PStmt]] = None
  private var _newStmtAtStart: Option[noApi.P[PStmt]] = None

  private var _preSpecification: Option[noApi.P[PExp]] = None
  private var _postSpecification: Option[noApi.P[PExp]] = None
  private var _invSpecification: Option[noApi.P[PExp]] = None
  private var _extendedKeywords: Set[String] = Set()


  /**
    * For more details regarding the functionality of each of these initial parser extensions
    * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
    */
  override lazy val newDeclAtStart = _newDeclAtStart match {
    case None => ParserPluginTemplate.defaultExtension
    case t: Option[noApi.P[PExtender]] => t.get
  }

  override lazy val newDeclAtEnd = _newDeclAtEnd match {
    case None => ParserPluginTemplate.defaultExtension
    case t: Option[noApi.P[PExtender]] => t.get
  }

  override lazy val newStmtAtEnd = _newStmtAtEnd match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case t: Option[noApi.P[PStmt]] => t.get
  }

  override lazy val newStmtAtStart = _newStmtAtStart match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case t: Option[noApi.P[PStmt]] => t.get
  }

  override lazy val newExpAtEnd = _newExpAtEnd match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[noApi.P[PExp]] => t.get
  }

  override lazy val newExpAtStart = _newExpAtStart match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[noApi.P[PExp]] => t.get
  }

  override lazy val postSpecification = _postSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[noApi.P[PExp]] => t.get
  }

  override lazy val preSpecification = _preSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[noApi.P[PExp]] => t.get
  }

  override lazy val invSpecification = _invSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[noApi.P[PExp]] => t.get
  }

  override lazy val extendedKeywords = _extendedKeywords

  def addNewDeclAtEnd(t: noApi.P[PExtender]) = _newDeclAtEnd match {
    case None => _newDeclAtEnd = Some(t)
    case f: Option[noApi.P[PExtender]] => _newDeclAtEnd = Some(P(f.get | t))
  }

  def addNewDeclAtStart(t: noApi.P[PExtender]) = _newDeclAtStart match {
    case None => _newDeclAtStart = Some(t)
    case f: Option[noApi.P[PExtender]] => _newDeclAtStart = Some(P(f.get | t))
  }

  def addNewExpAtEnd(t: noApi.P[PExp]) = _newExpAtEnd match {
    case None => _newExpAtEnd = Some(t)
    case f: Option[noApi.P[PExp]] => _newExpAtEnd = Some(P(f.get | t))
  }

  def addNewExpAtStart(t: noApi.P[PExp]) = _newExpAtStart match {
    case None => _newExpAtStart = Some(t)
    case f: Option[noApi.P[PExp]] => _newExpAtStart = Some(P(f.get | t))
  }

  def addNewStmtAtEnd(t: noApi.P[PStmt]) = _newStmtAtEnd match {
    case None => _newStmtAtEnd = Some(t)
    case f: Option[noApi.P[PStmt]] => _newStmtAtEnd = Some(P(f.get | t))
  }

  def addNewStmtAtStart(t: noApi.P[PStmt]) = _newStmtAtStart match {
    case None => _newStmtAtStart = Some(t)
    case f: Option[noApi.P[PStmt]] => _newStmtAtStart = Some(P(f.get | t))
  }

  def addNewPreCondition(t: noApi.P[PExp]) = _preSpecification match {
    case None => _preSpecification = Some(t)
    case f: Option[noApi.P[PExp]] => _preSpecification = Some(P(f.get | t))
  }

  def addNewPostCondition(t: noApi.P[PExp]) = _postSpecification match {
    case None => _postSpecification = Some(t)
    case f: Option[noApi.P[PExp]] => _postSpecification = Some(P(f.get | t))
  }

  def addNewInvariantCondition(t: noApi.P[PExp]) = _invSpecification match {
    case None => _invSpecification = Some(t)
    case f: Option[noApi.P[PExp]] => _invSpecification = Some(P(f.get | t))
  }

  def addNewKeywords(t: Set[String]) = {
    _extendedKeywords ++= t}

}