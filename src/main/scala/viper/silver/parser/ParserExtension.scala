// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import viper.silver.plugin._
import scala.collection.Set

import fastparse._

object ParserExtension extends ParserPluginTemplate {
//override val White = PWrapper { //?
//  import fastparse.all._
//  NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
//}

  /**
    * These private variables are the storage variables for each of the extensions.
    * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
    * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
    * can be referenced back.
    */
  private var _newDeclAtEnd: Option[P[PExtender]] = None
  private var _newDeclAtStart: Option[P[PExtender]] = None

  private var _newExpAtEnd: Option[P[PExp]] = None
  private var _newExpAtStart: Option[P[PExp]] = None

  private var _newStmtAtEnd: Option[P[PStmt]] = None
  private var _newStmtAtStart: Option[P[PStmt]] = None

  private var _preSpecification: Option[P[PExp]] = None
  private var _postSpecification: Option[P[PExp]] = None
  private var _invSpecification: Option[P[PExp]] = None
  private var _extendedKeywords: Set[String] = Set()


  /**
    * For more details regarding the functionality of each of these initial parser extensions
    * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
    */
  override def newDeclAtStart[_: P] = _newDeclAtStart match {
    case None => ParserPluginTemplate.defaultExtension
    case t: Option[P[PExtender]] => t.get
  }

  override def newDeclAtEnd[_: P] = _newDeclAtEnd match {
    case None => ParserPluginTemplate.defaultExtension
    case t: Option[P[PExtender]] => t.get
  }

  override def newStmtAtEnd[_: P] = _newStmtAtEnd match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case t: Option[P[PStmt]] => t.get
  }

  override def newStmtAtStart[_: P] = _newStmtAtStart match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case t: Option[P[PStmt]] => t.get
  }

  override def newExpAtEnd[_: P] = _newExpAtEnd match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[P[PExp]] => t.get
  }

  override def newExpAtStart[_: P] = _newExpAtStart match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[P[PExp]] => t.get
  }

  override def postSpecification[_: P] = _postSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[P[PExp]] => t.get
  }

  override def preSpecification[_: P] = _preSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[P[PExp]] => t.get
  }

  override def invSpecification[_: P] = _invSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case t: Option[P[PExp]] => t.get
  }

  override def extendedKeywords= _extendedKeywords

  def addNewDeclAtEnd[_: P](t: => P[PExtender]) = _newDeclAtEnd match {
    case None => _newDeclAtEnd = Some(t)
    case f: Option[P[PNode]] => _newDeclAtEnd = Some(P(f.get | t))
  }

  def addNewDeclAtStart[_: P](t: => P[PExtender]) = _newDeclAtStart match {
    case None => _newDeclAtStart = Some(t)
    case f: Option[P[PNode]] => _newDeclAtStart = Some(P(f.get | t))
  }

  def addNewExpAtEnd[_: P](t: => P[PExp]) = _newExpAtEnd match {
    case None => _newExpAtEnd = Some(t)
    case f: Option[P[PExp]] => _newExpAtEnd = Some(P(f.get | t))
  }

  def addNewExpAtStart[_: P](t: => P[PExp]) = _newExpAtStart match {
    case None => _newExpAtStart = Some(t)
    case f: Option[P[PExp]] => _newExpAtStart = Some(P(f.get | t))
  }

  def addNewStmtAtEnd[_: P](t: => P[PStmt]) = _newStmtAtEnd match {
    case None => _newStmtAtEnd = Some(t)
    case f: Option[P[PStmt]] => _newStmtAtEnd = Some(P(f.get | t))
  }

  def addNewStmtAtStart[_: P](t: => P[PStmt]) = _newStmtAtStart match {
    case None => _newStmtAtStart = Some(t)
    case f: Option[P[PStmt]] => _newStmtAtStart = Some(P(f.get | t))
  }

  def addNewPreCondition[_: P](t: => P[PExp]) = _preSpecification match {
    case None => _preSpecification = Some(t)
    case f: Option[P[PExp]] => _preSpecification = Some(P(f.get | t))
  }

  def addNewPostCondition[_: P](t: => P[PExp]) = _postSpecification match {
    case None => _postSpecification = Some(t)
    case f: Option[P[PExp]] => _postSpecification = Some(P(f.get | t))
  }

  def addNewInvariantCondition[_: P](t: => P[PExp]) = _invSpecification match {
    case None => _invSpecification = Some(t)
    case f: Option[P[PExp]] => _invSpecification = Some(P(f.get | t))
  }

  def addNewKeywords(t: Set[String]) = {
    _extendedKeywords ++= t}
}