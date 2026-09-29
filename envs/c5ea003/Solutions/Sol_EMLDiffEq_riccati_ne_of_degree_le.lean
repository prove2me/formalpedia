-- Prove2me | solution 1 for EMLDiffEq.riccati_ne_of_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:02:03.990667+00:00
-- url     : https://prove2.me/submissions/71b6ecd9-db66-4f9f-acf4-3546da7c25db

-- Sol generated from Applications/EML/EMLDifferentialEquations.lean
import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations
import Theorems.Thm_EMLDiffEq_degree_wronskianNum_lt

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


/-- A polynomial of odd natural degree is nonzero. -/
theorem ne_zero_of_odd_natDegree {r : K[X]} (hr : Odd r.natDegree) : r ≠ 0 := by
  rintro rfl
  simp only [Polynomial.natDegree_zero] at hr
  obtain ⟨k, hk⟩ := hr
  omega









/-! ## 4. From analysis to algebra: Airy has no EML exponential solution -/



/-! ## 5. Sharpness of the odd-degree hypothesis -/





open EMLDiffEq in
theorem solution(r P Q : K[X]) (hr : Odd r.natDegree) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hle : Q.natDegree ≤ P.natDegree) :
    derivative P * Q - P * derivative Q + P ^ 2 ≠ r * Q ^ 2 := by
  intro heq
  have hr0 : r ≠ 0 := ne_zero_of_odd_natDegree hr
  have hW := degree_wronskianNum_lt P Q hP hQ
  have hlt' : (derivative P * Q - P * derivative Q).degree < (P ^ 2).degree := by
    refine lt_of_lt_of_le hW ?_
    rw [sq, Polynomial.degree_mul, Polynomial.degree_eq_natDegree hP,
      Polynomial.degree_eq_natDegree hQ]
    exact_mod_cast Nat.add_le_add_left hle P.natDegree
  have hdeg : (derivative P * Q - P * derivative Q + P ^ 2).degree = (P ^ 2).degree :=
    Polynomial.degree_add_eq_right_of_degree_lt hlt'
  rw [heq] at hdeg
  have h1 : (r * Q ^ 2).natDegree = (P ^ 2).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq hdeg
  rw [Polynomial.natDegree_mul hr0 (pow_ne_zero 2 hQ), Polynomial.natDegree_pow,
    Polynomial.natDegree_pow] at h1
  obtain ⟨k, hk⟩ := hr
  omega
