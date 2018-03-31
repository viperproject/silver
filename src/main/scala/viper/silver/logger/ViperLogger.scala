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
  * @param  name  the name of the logger
  * @param  file  either [[Some]] file to which the logger will be written,
  *               or [[None]], if which case logs will be written to STDOUT.
  * @param  level the level of detail for this logger (should be one of the
  *               following values:
  *               @see [[ch.qos.logback.classic.Level.toLevel]])
  *
  * @return       the logger factory that will lazily produce a singleton
  *               logger once [[viper.silver.logger.ViperLogger.get]] is evaluated.
  */
class ViperLogger(val name: String, val file: Option[String], val level: String) {

  lazy val get: Logger = createLoggerFor(name, file, level)

  /** Borrowed from https://stackoverflow.com/questions/16910955/programmatically-configure-logback-appender */
  private def createLoggerFor(string: String, file: Option[String], str_level: String) = {
    val lc = LoggerFactory.getILoggerFactory.asInstanceOf[LoggerContext]
    val ple = new PatternLayoutEncoder
    ple.setPattern("%date %level [%thread] %logger{10} [%file:%line] %msg%n")
    ple.setContext(lc)
    ple.start()
    val logger = LoggerFactory.getLogger(string).asInstanceOf[Logger]
    file match {
      case Some(f_name) =>
        val fileAppender: FileAppender[ILoggingEvent] = new FileAppender[ILoggingEvent]
        fileAppender.setFile(f_name)
        fileAppender.setEncoder(ple)
        fileAppender.setContext(lc)
        fileAppender.start()
        logger.addAppender(fileAppender)
      case None =>
        val stdOutApender = new ConsoleAppender[ILoggingEvent]
        stdOutApender.setTarget("System.out")
        stdOutApender.setEncoder(ple)
        stdOutApender.setContext(lc)
        stdOutApender.start()
        logger.addAppender(stdOutApender)
    }
    logger.setLevel(toLevel(str_level))
    logger.setAdditive(false) /* set to true if root should log too */
    logger
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
