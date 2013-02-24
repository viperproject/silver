
name := "sil"

organization  := "semper"

version := "0.1-SNAPSHOT"

scalaVersion := "2.10.0"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1" withJavadoc() withSources()

libraryDependencies += "com.googlecode.kiama" % "kiama_2.10" % "1.4.0"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

scalacOptions += "-unchecked"

scalacOptions += "-Dscalac.patmat.analysisBudget=2048"
