// SIL AST

name := "silast"

version := "0.1"

scalaVersion := "2.9.1"

scalaSource <<= baseDirectory(_ / "src")

scalaSource in Compile <<= scalaSource