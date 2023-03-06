package propel

import ast.*
import printing.*
import evaluator.*

import org.scalatest.Ignore
import org.scalatest.funsuite.AnyFunSuite

class SuccessfulPropertyChecks extends AnyFunSuite:
  def check(expr: Term) =
    val errors = properties.check(expr, printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
    if errors.nonEmpty then fail(errors)

  benchmarks() ++ examples foreach { (benchmark, expr) =>
    if !(FailingPropertyChecks.names contains benchmark) then test(benchmark) { check(expr) }
  }

object FailingPropertyChecks:
  val names = Set(
    "nat_add2p_acc",
    "nat_add3p_acc",
    "nat_mult2p_acc",
    "nat_mult3p",
    "nat_max_acc",
    "nat_lwwreg_acc",
    "bv_lwwreg",
    "tip_nat_times_alt",
    "tip_nat_times_acc",
    "tip_weird_nat_times",
    "tip_bin_times",
    "tip_int_plus",
    "tip_int_times",
    "nat_lwwreg_alt3")

@Ignore
class FailingPropertyChecks extends AnyFunSuite:
  def check(expr: Term) =
    val errors = properties.check(expr, printDeductionDebugInfo = false, printReductionDebugInfo = false).showErrors
    if errors.nonEmpty then fail(errors)

  benchmarks() ++ examples foreach { (benchmark, expr) =>
    if FailingPropertyChecks.names contains benchmark then test(benchmark) { check(expr) }
  }
