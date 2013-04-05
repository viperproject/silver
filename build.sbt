
name := "sil"

organization  := "semper"

version := "0.1-SNAPSHOT"

scalaVersion := "2.10.0"

libraryDependencies += "org.scalatest" %% "scalatest" % "1.9.1"

libraryDependencies += "com.googlecode.kiama" % "kiama_2.10" % "1.4.0"

libraryDependencies += "org.rogach" %% "scallop" % "0.8.1"

scalacOptions += "-deprecation"

scalacOptions += "-feature"

scalacOptions += "-unchecked"
