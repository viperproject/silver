// SIL AST

name := "silast"

organization  := "pm.inf.ethz.ch"

version := "0.1-SNAPSHOT"

scalaVersion := "2.9.1"

scalaSource <<= baseDirectory(_ / "src")

scalaSource in Compile <<= scalaSource