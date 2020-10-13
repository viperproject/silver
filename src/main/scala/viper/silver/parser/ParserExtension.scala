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

  import ParserPluginTemplate._

  /**
    * These private variables are the storage variables for each of the extensions.
    * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
    * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
    * can be referenced back.
    */
  private var _newDeclAtEnd: Option[Extension[PExtender]] = None
  private var _newDeclAtStart: Option[Extension[PExtender]] = None

  private var _newExpAtEnd: Option[Extension[PExp]] = None
  private var _newExpAtStart: Option[Extension[PExp]] = None

  private var _newStmtAtEnd: Option[Extension[PStmt]] = None
  private var _newStmtAtStart: Option[Extension[PStmt]] = None

  private var _preSpecification: Option[Extension[PExp]] = None
  private var _postSpecification: Option[Extension[PExp]] = None
  private var _invSpecification: Option[Extension[PExp]] = None

  private var _extendedKeywords: Set[String] = Set()


  /**
    * For more details regarding the functionality of each of these initial parser extensions
    * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
    */
  override def newDeclAtStart : Extension[PExtender] = _newDeclAtStart match {
    case None => ParserPluginTemplate.defaultExtension
    case Some(ext) => ext
  }

  override def newDeclAtEnd : Extension[PExtender] = _newDeclAtEnd match {
    case None => ParserPluginTemplate.defaultExtension
    case Some(ext) => ext
  }

  override def newStmtAtEnd : Extension[PStmt] = _newStmtAtEnd match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case Some(ext) => ext
  }

  override def newStmtAtStart : Extension[PStmt] = _newStmtAtStart match {
    case None => ParserPluginTemplate.defaultStmtExtension
    case Some(ext) => ext
  }

  override def newExpAtEnd : Extension[PExp] = _newExpAtEnd match {
    case None => ParserPluginTemplate.defaultExpExtension
    case Some(ext) => ext
  }

  override def newExpAtStart : Extension[PExp] = _newExpAtStart match {
    case None => ParserPluginTemplate.defaultExpExtension
    case Some(ext) => ext
  }

  override def postSpecification : Extension[PExp] = _postSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case Some(ext) => ext
  }

  override def preSpecification : Extension[PExp] = _preSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case Some(ext) => ext
  }

  override def invSpecification : Extension[PExp] = _invSpecification match {
    case None => ParserPluginTemplate.defaultExpExtension
    case Some(ext) => ext
  }

  override def extendedKeywords : Set[String] = _extendedKeywords

  def addNewDeclAtEnd(t: => Extension[PExtender]) : Unit = _newDeclAtEnd match { //? Check if it is needed (already is a function). Try to remove.
    case None => _newDeclAtEnd = Some(t)
    case Some(s) => _newDeclAtEnd = Some(combine(s, t))
  }

  def addNewDeclAtStart(t: => Extension[PExtender]) : Unit = _newDeclAtStart match {
    case None => _newDeclAtStart = Some(t)
    case Some(s) => _newDeclAtStart = Some(combine(s, t))
  }

  def addNewExpAtEnd(t: => Extension[PExp]) : Unit = _newExpAtEnd match {
    case None => _newExpAtEnd = Some(t)
    case Some(s) => _newExpAtEnd = Some(combine(s, t))
  }

  def addNewExpAtStart(t: => Extension[PExp]) : Unit = _newExpAtStart match {
    case None => _newExpAtStart = Some(t)
    case Some(s) => _newExpAtStart = Some(combine(s, t))
  }

  def addNewStmtAtEnd(t: => Extension[PStmt]) : Unit = _newStmtAtEnd match {
    case None => _newStmtAtEnd = Some(t)
    case Some(s) => _newStmtAtEnd = Some(combine(s, t))
  }

  def addNewStmtAtStart(t: => Extension[PStmt]) : Unit = _newStmtAtStart match {
    case None => _newStmtAtStart = Some(t)
    case Some(s) => _newStmtAtStart = Some(combine(s, t))
  }

  def addNewPreCondition(t: => Extension[PExp]) : Unit = _preSpecification match {
    case None => _preSpecification = Some(t)
    case Some(s) => _preSpecification = Some(combine(s, t))
  }

  def addNewPostCondition(t: => Extension[PExp]) : Unit = _postSpecification match {
    case None => _postSpecification = Some(t)
    case Some(s) => _postSpecification = Some(combine(s, t))
  }

  def addNewInvariantCondition(t: => Extension[PExp]) : Unit = _invSpecification match {
    case None => _invSpecification = Some(t)
    case Some(s) => _invSpecification = Some(combine(s, t))
  }

  def addNewKeywords(t : Set[String]) : Unit = {
    _extendedKeywords ++= t
  }
}