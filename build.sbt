// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

// Settings common to Silver and backends
// Compilation settings
ThisBuild / scalaVersion := "2.12.7"
ThisBuild / scalacOptions ++= Seq(
  "-deprecation",                     // Warn when using deprecated language features
  "-unchecked",                       // Warn on generated code assumptions
  "-feature",                         // Warn on features that requires explicit import
  "-Ywarn-unused-import",             // Warn on unused imports
  "-Ypatmat-exhaust-depth", "40"      // Increase depth of pattern matching analysis
)

// Publishing settings

// Allows 'publishLocal' SBT command to include test artifacts in a dedicated JAR file
// (whose name is postfixed by 'test-source') and publish it in the local Ivy repository.
// This JAR file contains all classes and resources for testing and projects like Carbon
// and Silicon can rely on it to access the test suit implemented in Silver.
ThisBuild / Test / publishArtifact := true

// Silver specific project settings
lazy val silver = (project in file("."))
  .settings(
    // General settings
    name := "silver",
    organization := "viper",
    version := "0.1-SNAPSHOT",

    // Fork test to a different JVM than SBT's, avoiding SBT's classpath interfering with
    // classpath used by Scala's reflection.
    Test / fork := true,

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

    // Test settings.
    Test / parallelExecution := false,

    // Assembly settings
    assembly / assemblyJarName := "silver.jar",
    assembly / test := {},
  )
