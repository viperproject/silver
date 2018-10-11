// Settings common to Silver and backends
// Compilation settings
ThisBuild / scalaVersion := "2.12.6"
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
    name := "silver",           //? Silicon depends on it? Capitalize otherwise.
    organization := "viper",    //? Silicon depends on it? Use ETH otherwise.
    version := "0.1-SNAPSHOT",  //? Silicon depends on it? Establish otherwise.

    // Compilation settings (old)
    //libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,             // Scala
    //libraryDependencies += "org.scalatest" %% "scalatest" % "2.2.1",                            // Testing
    //libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.5",    // Parsing
    //libraryDependencies += "com.lihaoyi" %% "fastparse" % "0.3.7",                              // Parsing
    //libraryDependencies += "org.rogach" %% "scallop" % "2.0.7",                                 // CLI parsing
    //libraryDependencies += "commons-io" % "commons-io" % "2.5",                                 // I/O
    //libraryDependencies += "com.google.guava" % "guava" % "17.0",                               // Collections
    //libraryDependencies += "org.jgrapht" % "jgrapht-core" % "0.9.1",                            // Graphs
    //libraryDependencies += "org.slf4j" % "slf4j-api" % "1.7.12",                                // Logging
    //libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.1.7",                      // Logging

    // Compilation settings
    libraryDependencies += "org.scala-lang" % "scala-reflect" % scalaVersion.value,             // Scala
    libraryDependencies += "org.scalatest" %% "scalatest" % "3.0.5",                            // Testing
    //libraryDependencies += "org.scalatest" % "scalatest_2.12" % "3.0.5" % "test",               // Testing
    libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.1",    // Parsing
    libraryDependencies += "com.lihaoyi" %% "fastparse" % "1.0.0",                              // Parsing
    libraryDependencies += "org.rogach" %% "scallop" % "3.1.3",                                 // CLI parsing
    libraryDependencies += "commons-io" % "commons-io" % "2.6",                                 // I/O
    libraryDependencies += "com.google.guava" % "guava" % "26.0-jre",                           // Collections
    libraryDependencies += "org.jgrapht" % "jgrapht-core" % "1.2.0",                            // Graphs
    libraryDependencies += "org.slf4j" % "slf4j-api" % "1.7.25",                                // Logging
    libraryDependencies += "ch.qos.logback" % "logback-classic" % "1.2.3",                      // Logging

    // Test settings
    Test / parallelExecution := false
  )






//organization  := "viper"
//version := "0.1-SNAPSHOT"
//libraryDependencies += "com.typesafe.scala-logging" %% "scala-logging" % "3.5.0" // Logging Frontend




//scalacOptions += "-deprecation"
//scalacOptions += "-feature"
//scalacOptions += "-unchecked"
//scalacOptions ++= Seq("-Ypatmat-exhaust-depth", "off")




// Make publish-local also create a test artifact, i.e., put a jar-file into the local Ivy
// repository that contains all classes and resources relevant for testing.
// Other projects, e.g., Carbon or Silicon, can then depend on the Sil test artifact, which
// allows them to access the Sil test suite.

//publishArtifact in Test := true




//(Test, packageBin) := true

// Avoid problems with racy initialisation of SLF4J:
//    http://stackoverflow.com/a/12095245
//    https://github.com/typesafehub/scalalogging/issues/23

//testOptions in Test += Tests.Setup(classLoader =>
//  classLoader
//    .loadClass("org.slf4j.LoggerFactory")
//    .getMethod("getLogger", classLoader.loadClass("java.lang.String"))
//    .invoke(null, "ROOT"))
//
