// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

// Settings common to Silver and backends
// Compilation settings

ThisBuild / scalaVersion := "2.13.18"
ThisBuild / scalacOptions ++= Seq(
  "-encoding", "UTF-8",               // Enforce UTF-8, instead of relying on properly set locales
  "-deprecation",                     // Warn when using deprecated language features
  "-unchecked",                       // Warn on generated code assumptions
  "-feature",                         // Warn on features that requires explicit import
  "-Wunused",                         // Warn on unused imports
  "-Ypatmat-exhaust-depth", "40",     // Increase depth of pattern matching analysis
)

// Enforce UTF-8, instead of relying on properly set locales
ThisBuild / javacOptions ++= Seq("-encoding", "UTF-8", "-charset", "UTF-8", "-docencoding", "UTF-8")
ThisBuild / javaOptions  ++= Seq("-Dfile.encoding=UTF-8")

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

    // Treat warnings as errors to guarantee code quality in future changes. Note that this is
    // deliberately scoped to the Silver project rather than added to the `ThisBuild / scalacOptions`
    // above: this file is also loaded when a backend (e.g. Silicon or Carbon) includes Silver as a
    // subproject, and settings in the `ThisBuild` scope would then apply to the backend's own
    // sources as well, breaking its build on warnings that are unrelated to Silver.
    scalacOptions += "-Xfatal-warnings",

    // Scaladoc still reports a number of pre-existing warnings (mostly links that cannot be
    // resolved), so `-Xfatal-warnings` is not applied to it; otherwise `doc`, and with it
    // `publishLocal`, would fail.
    Compile / doc / scalacOptions -= "-Xfatal-warnings",
    Test / doc / scalacOptions -= "-Xfatal-warnings",

    // Compilation settings
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,             // Scala
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.2",                            // Testing
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2",    // Parsing
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "2.2.2",                              // Parsing
    libraryDependencies += "org.rogach" %% "scallop" % "4.0.4",                                 // CLI parsing
    libraryDependencies += "commons-io" % "commons-io" % "2.8.0",                               // I/O
    libraryDependencies += "com.google.guava" % "guava" % "29.0-jre",                           // Collections
    libraryDependencies += "org.jgrapht" % "jgrapht-core" % "1.5.0",                            // Graphs
    libraryDependencies += "org.slf4j" % "slf4j-api" % "1.7.30",                                // Logging
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",                      // Logging
    libraryDependencies += "com.lihaoyi" %% "requests" % "0.3.0",                               // Data collection
    libraryDependencies += "com.lihaoyi" %% "upickle" % "1.0.0",                                // Data collection

    // Test settings.
    Test / parallelExecution := false,

    // Assembly settings
    assembly / assemblyJarName := "silver.jar",
    assembly / test := {},
  )

