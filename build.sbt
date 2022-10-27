name := "propel"

scalaVersion := "3.2.0"

scalacOptions ++= Seq("-feature", "-deprecation", "-unchecked", "-Yexplicit-nulls")

run := (Test / run).evaluated
runMain := (Test / runMain).evaluated
compile := (Test / compile).value
