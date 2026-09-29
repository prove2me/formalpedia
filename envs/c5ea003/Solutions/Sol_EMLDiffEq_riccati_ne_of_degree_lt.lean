-- Prove2me | solution 1 for EMLDiffEq.riccati_ne_of_degree_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:02:04.858134+00:00
-- url     : https://prove2.me/submissions/28311a3e-62b4-43b2-8535-b7424848dd27

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
    (hlt : P.natDegree < Q.natDegree) :
    derivative P * Q - P * derivative Q + P ^ 2 ≠ r * Q ^ 2 := by
  intro heq
  have hr0 : r ≠ 0 := ne_zero_of_odd_natDegree hr
  have hr1 : 1 ≤ r.natDegree := by obtain ⟨k, hk⟩ := hr; omega
  have hRHS : (r * Q ^ 2).degree = ((r.natDegree + 2 * Q.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero hr0 (pow_ne_zero 2 hQ)),
      Polynomial.natDegree_mul hr0 (pow_ne_zero 2 hQ), Polynomial.natDegree_pow]
  have hPQ : P.degree + Q.degree = ((P.natDegree + Q.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hP, Polynomial.degree_eq_natDegree hQ]
    push_cast
    ring
  have hP2 : (P ^ 2).degree = ((2 * P.natDegree : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree (pow_ne_zero 2 hP), Polynomial.natDegree_pow]
  have hW := degree_wronskianNum_lt P Q hP hQ
  rw [hPQ] at hW
  have hd1 : (derivative P * Q - P * derivative Q).degree < (r * Q ^ 2).degree := by
    refine lt_of_lt_of_le hW ?_
    rw [hRHS]
    exact_mod_cast (by omega : P.natDegree + Q.natDegree ≤ r.natDegree + 2 * Q.natDegree)
  have hd2 : (P ^ 2).degree < (r * Q ^ 2).degree := by
    rw [hRHS, hP2]
    exact_mod_cast (by omega : 2 * P.natDegree < r.natDegree + 2 * Q.natDegree)
  have hfin : (derivative P * Q - P * derivative Q + P ^ 2).degree < (r * Q ^ 2).degree :=
    lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt hd1 hd2)
  rw [heq] at hfin
  exact lt_irrefl _ hfin
