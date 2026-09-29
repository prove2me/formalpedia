-- Prove2me | solution 1 for EMLDiffEq.degree_wronskianNum_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:56:51.479409+00:00
-- url     : https://prove2.me/submissions/b6526de9-bda1-4292-ae3c-e88d53abfedf

-- Sol generated from Applications/EML/EMLDifferentialEquations.lean
import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations

/-!
# EML Differential Equations

Exponential–logarithmic (**EML**) functions are the real functions built from the
identity, real constants, `+`, `*`, `⁻¹`, `Real.exp` and `Real.log`.  This file
develops the differential calculus of that class and uses it to analyse the
second-order linear equation

  `y'' = r · y`,   `r` a polynomial,

with the **Airy equation** `y'' = x · y` as the guiding example.

## Contents

* `EMLExpr`, `EMLExpr.eval`, `EMLExpr.D`, `EMLExpr.Regular` — a syntax for EML
  functions, its interpretation, its *symbolic* derivative and the (pointwise)
  regularity predicate saying that all inversions and logarithms occurring in an
  expression have nonzero argument at a point.
* `EMLExpr.hasDerivAt_eval` — **correctness of symbolic differentiation**: at a
  regular point the analytic derivative of `eval e` is `eval (D e)`.  In
  particular the class of EML functions is closed under differentiation
  (`EMLExpr.Regular.D`).
* `EMLExpr.exp_solves_firstOrder` and `EMLExpr.firstOrder_unique` — the complete
  solution theory of the first-order linear EML equation `y' = c · y`: the
  exponential of an antiderivative solves it, and every solution is a constant
  multiple of that one.
* `riccati_no_rational_solution` — the **algebraic Kovacic obstruction**: if
  `r` is a polynomial of odd degree then the Riccati equation `u' + u² = r` has
  no solution `u = P/Q` in the field of rational functions.
* `airy_no_rational_logDeriv` — the analytic form: no nowhere-vanishing solution
  of `y'' = x·y` has a rational logarithmic derivative.
* `airy_no_eml_exponential_solution` — consequently the Airy equation has no
  solution of the EML shape `y = exp ∘ F` with `F'` rational; this is exactly
  the failure of the first Kovacic case for Airy's equation.
* `riccati_odd_degree_sharp`, `exp_half_sq_solves` — sharpness: for the
  even-degree coefficient `r = x² + 1` the Riccati equation *does* have the
  rational solution `u = x`, and `y = exp (x²/2)` is a genuine EML solution of
  `y'' = (x²+1) y`.
-/

open EMLDiffEq

open Polynomial

/-! ## 1. Syntax and calculus of EML functions -/


open EMLExpr







/-! ## 2. First-order linear EML equations -/




/-! ## 3. The algebraic Kovacic obstruction -/


variable {K : Type*} [Field K]











/-! ## 4. From analysis to algebra: Airy has no EML exponential solution -/



/-! ## 5. Sharpness of the odd-degree hypothesis -/





open EMLDiffEq in
theorem solution(P Q : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    (derivative P * Q - P * derivative Q).degree < P.degree + Q.degree := by
  have h1 : (derivative P * Q).degree < P.degree + Q.degree := by
    have := Polynomial.degree_derivative_lt hP
    calc (derivative P * Q).degree ≤ (derivative P).degree + Q.degree :=
          Polynomial.degree_mul_le _ _
      _ < P.degree + Q.degree := by
          exact WithBot.add_lt_add_right (by simpa using hQ) this
  have h2 : (P * derivative Q).degree < P.degree + Q.degree := by
    have := Polynomial.degree_derivative_lt hQ
    calc (P * derivative Q).degree ≤ P.degree + (derivative Q).degree :=
          Polynomial.degree_mul_le _ _
      _ < P.degree + Q.degree := by
          exact WithBot.add_lt_add_left (by simpa using hP) this
  exact lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt h1 h2)
