scalaVersion := "3.2.0"

libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.0.0"

libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.14"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.14" % "test"

libraryDependencies += "org.scalatest" %% "scalatest-flatspec" % "3.2.14" % "test"

Test / logBuffered := false

