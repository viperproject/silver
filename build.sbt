
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

libraryDependencies += "org.slf4j" % "slf4j-api" % "1.7.12"
libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.1.7" // Logging Backend
libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0" // Logging Frontend

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

// Avoid problems with racy initialisation of SLF4J:
//    http://stackoverflow.com/a/12095245
//    https://github.com/typesafehub/scalalogging/issues/23
testOptions in Test += Tests.Setup(classLoader =>
  classLoader
    .loadClass("org.slf4j.LoggerFactory")
    .getMethod("getLogger", classLoader.loadClass("java.lang.String"))
    .invoke(null, "ROOT"))

parallelExecution in Test := false
