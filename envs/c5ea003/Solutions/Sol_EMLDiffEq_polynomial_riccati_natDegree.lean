-- Prove2me | solution 1 for EMLDiffEq.polynomial_riccati_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:02:05.469129+00:00
-- url     : https://prove2.me/submissions/6fee130c-2128-4708-b4d5-76acdf2a3a6a

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
theorem solution(r u : K[X]) (hu : u ≠ 0)
    (h : derivative u + u ^ 2 = r) :
    r.natDegree = 2 * u.natDegree ∧ r.leadingCoeff = u.leadingCoeff ^ 2 := by
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have hlt : (derivative u).degree < (u ^ 2).degree := by
    refine lt_of_lt_of_le (Polynomial.degree_derivative_lt hu) ?_
    rw [sq, Polynomial.degree_mul, Polynomial.degree_eq_natDegree hu]
    exact_mod_cast Nat.le_add_left u.natDegree u.natDegree
  constructor
  · have hd : r.natDegree = (u ^ 2).natDegree := by
      rw [← h]
      exact Polynomial.natDegree_eq_of_degree_eq
        (Polynomial.degree_add_eq_right_of_degree_lt hlt)
    rw [hd, Polynomial.natDegree_pow]
  · rw [← h, Polynomial.leadingCoeff_add_of_degree_lt hlt, Polynomial.leadingCoeff_pow]
