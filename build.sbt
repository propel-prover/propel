import scala.scalanative.build._

ThisBuild / scalaVersion := "3.2.0"

ThisBuild / scalacOptions ++= Seq("-feature", "-deprecation", "-unchecked", "-Yexplicit-nulls")

ThisBuild / nativeConfig ~= { _.withLTO(LTO.thin).withMode(Mode.releaseFast) }

lazy val propelCrossProject = crossProject(JVMPlatform, NativePlatform)
  .crossType(CrossType.Pure)
  .in(file("."))
  .jvmConfigure(_.withId("propelJVM"))
  .nativeConfigure(_.withId("propelNative"))
  .nativeSettings(Compile / nativeLink / artifactPath ~= { file => file.getParentFile / file.getName.replace("propelcrossproject-out", "propel") })

val propelJVM = propelCrossProject.jvm
val propelNative = propelCrossProject.native

lazy val propel = project
  .in(file("."))
  .aggregate(propelJVM, propelNative)
  .settings(
    run / aggregate := false,
    runMain / aggregate := false,
    compile / aggregate := false)

run := (propelJVM / Test / run).evaluated
runMain := (propelJVM / Test / runMain).evaluated
compile := (propelJVM / Test / compile).value
