import scala.scalanative.build._

ThisBuild / scalaVersion := "3.2.0"

ThisBuild / scalacOptions ++= Seq("-feature", "-deprecation", "-unchecked", "-Yexplicit-nulls")

ThisBuild / nativeConfig ~= { _.withLTO(LTO.thin).withMode(Mode.releaseFast) }

ThisBuild / libraryDependencies += "org.scalatest" %%% "scalatest" % "3.2.15" % Test

ThisBuild / Test / logBuffered := false

ThisBuild / Test / parallelExecution := false

lazy val propelCrossProject = crossProject(JVMPlatform, NativePlatform)
  .crossType(CrossType.Pure)
  .in(file("."))
  .jvmConfigure(_.withId("propelJVM"))
  .nativeConfigure(_.withId("propelNative"))
  .nativeSettings(
    Test / mainClass := Some("propel.benchmark"),
    Test / loadedTestFrameworks := Map.empty,
    Test / nativeLink / artifactPath ~= { file => file.getParentFile / file.getName.replace("propelcrossproject-test-out", "propel") })

lazy val propelJVM = propelCrossProject.jvm
lazy val propelNative = propelCrossProject.native

lazy val propel = project
  .in(file("."))
  .aggregate(propelJVM, propelNative)
  .settings(
    run / aggregate := false,
    runMain / aggregate := false,
    test / aggregate := false,
    testOnly / aggregate := false,
    compile / aggregate := false,
    nativeLink / aggregate := false)

run := (propelJVM / Test / run).evaluated
runMain := (propelJVM / Test / runMain).evaluated
test := (propelJVM / Test / test).value
testOnly := (propelJVM / Test / testOnly).evaluated
compile := (propelJVM / Test / compile).value
nativeLink := (propelNative / Test / nativeLink).value
