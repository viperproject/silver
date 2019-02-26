// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.logger

import ch.qos.logback.classic.{Logger, LoggerContext}
import ch.qos.logback.classic.encoder.PatternLayoutEncoder
import ch.qos.logback.classic.spi.ILoggingEvent
import ch.qos.logback.classic.Level.toLevel
import ch.qos.logback.core.{ConsoleAppender, FileAppender}
import org.slf4j.LoggerFactory

/**
  * Factory for [[Logger]] instances.
  *
  * @param  name  The name of the logger.
  * @param  file  Either [[Some]] file to which the logger will be written,
  *               or [[None]], in which case logs will be written to STDOUT.
  * @param  level The level of detail for this logger (should be one of the
  *               following values:
  *               @see [[ch.qos.logback.classic.Level.toLevel]])
  *
  * @return       The logger factory that will lazily produce a singleton
  *               logger once [[viper.silver.logger.ViperLogger::get]] is evaluated.
  *
  * @author       Based on https://stackoverflow.com/questions/16910955/programmatically-configure-logback-appender
  */
class ViperLogger(val name: String, val file: Option[String], val level: String) {

  lazy val get: Logger = createLoggerFor(name, file, level)

  /** Borrowed from  */
  private def createLoggerFor(string: String, file: Option[String], str_level: String) = {
    val lc = LoggerFactory.getILoggerFactory.asInstanceOf[LoggerContext]
    val logger = LoggerFactory.getLogger(string).asInstanceOf[Logger]
    file match {
      case Some(f_name) =>
        val fileAppender: FileAppender[ILoggingEvent] = new FileAppender[ILoggingEvent]
        fileAppender.setFile(f_name)
        fileAppender.setEncoder( createEncoder(lc, "%date %level [%thread] %logger{10} [%file:%line] %msg%n") )
        fileAppender.setContext(lc)
        fileAppender.start()
        logger.addAppender(fileAppender)
      case None =>
        val stdOutApender = new ConsoleAppender[ILoggingEvent]
        stdOutApender.setTarget("System.out")
        stdOutApender.setEncoder( createEncoder(lc, "%msg%n") )
        stdOutApender.setContext(lc)
        stdOutApender.start()
        logger.addAppender(stdOutApender)
    }
    logger.setLevel(toLevel(str_level))
    logger.setAdditive(false) /* set to true if root should log too */
    logger
  }

  private def createEncoder(lc: LoggerContext, pattern: String): PatternLayoutEncoder = {
    val ple = new PatternLayoutEncoder
    ple.setPattern(pattern)
    ple.setContext(lc)
    ple.start()
    ple
  }
}

object ViperLogger {
  def apply(name: String, file: String, level: String = "ERROR"): ViperLogger =
    new ViperLogger(name, Some(file), level)
}

object ViperStdOutLogger {
  def apply(name: String, level: String = "ERROR"): ViperLogger =
    new ViperLogger(name, None, level)
}

object SilentLogger {
  def apply() = new ViperLogger("", None, "OFF")
}
