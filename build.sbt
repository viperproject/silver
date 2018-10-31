// Settings common to Silver and backends
// Compilation settings
ThisBuild / scalaVersion := "2.12.7"
ThisBuild / scalacOptions ++= Seq(
  "-deprecation",                     // Warn when using deprecated language features
  "-unchecked",                       // Warn on generated code assumptions
  "-feature",                         // Warn on features that requires explicit import
  "-Ywarn-unused-import"              // Warn on unused imports
)


// Silver specific project settings
lazy val silver = (project in file("."))
  .settings(
    // General settings
    name := "silver",
    organization := "viper",
    version := "0.1-SNAPSHOT",

    // Compilation settings
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,             // Scala
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5",                            // Testing
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1",    // Parsing
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "1.0.0",                              // Parsing
    libraryDependencies += "org.rogach" %% "scallop" % "3.1.3",                                 // CLI parsing
    libraryDependencies += "commons-io" % "commons-io" % "2.6",                                 // I/O
    libraryDependencies += "com.google.guava" % "guava" % "27.0-jre",                           // Collections
    libraryDependencies += "org.jgrapht" % "jgrapht-core" % "1.2.0",                            // Graphs
    libraryDependencies += "org.slf4j" % "slf4j-api" % "1.7.25",                                // Logging
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",                      // Logging

    // Test settings
    Test / parallelExecution := false
  )
