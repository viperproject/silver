
name := "silver"

organization  := "viper"

version := "0.1-SNAPSHOT"

scalaVersion := "2.11.4"

libraryDependencies += "org.scalatest" %% "scalatest" % "2.2.1"

libraryDependencies += "com.googlecode.kiama" % "kiama_2.11" % "1.8.0"

libraryDependencies += "org.rogach" %% "scallop" % "0.9.5"

libraryDependencies += "org.jgrapht" % "jgrapht-core" % "0.9.0"

libraryDependencies += "org.jgrapht" % "jgrapht-ext" % "0.9.0"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.2"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

scalacOptions += "-unchecked"

scalacOptions += "-Dscalac.patmat.analysisBudget=4096"

// Make publish-local also create a test artifact, i.e., put a jar-file into the local Ivy
// repository that contains all classes and resources relevant for testing.
// Other projects, e.g., Carbon or Silicon, can then depend on the Sil test artifact, which
// allows them to access the Sil test suite.
publishArtifact in (Test, packageBin) := true
