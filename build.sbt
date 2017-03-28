
name := "silver"

organization  := "viper"

version := "0.1-SNAPSHOT"

scalaVersion := "2.11.8"

libraryDependencies += "org.scalatest" %% "scalatest" % "2.2.1"

libraryDependencies += "org.rogach" %% "scallop" % "2.0.7"

libraryDependencies += "org.jgrapht" % "jgrapht-core" % "0.9.1"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.5"

libraryDependencies += "commons-io" % "commons-io" % "2.5"

libraryDependencies += "com.lihaoyi" %% "fastparse" % "0.3.7"
libraryDependencies += "com.google.guava" % "guava" % "17.0"

libraryDependencies += "org.slf4s" %% "slf4s-api" % "1.7.12"
libraryDependencies += "org.slf4j" % "slf4j-log4j12" % "1.7.22"

libraryDependencies += "org.apache.commons" % "commons-pool2" % "2.4.2"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

scalacOptions += "-unchecked"

scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "off")

// Make publish-local also create a test artifact, i.e., put a jar-file into the local Ivy
// repository that contains all classes and resources relevant for testing.
// Other projects, e.g., Carbon or Silicon, can then depend on the Sil test artifact, which
// allows them to access the Sil test suite.
publishArtifact in Test := true
//(Test, packageBin) := true
