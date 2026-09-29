-- Prove2me | solution 1 for EMLDiffEq.airy_no_rational_logDeriv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:00:03.090164+00:00
-- url     : https://prove2.me/submissions/9ef06236-92b3-4d5c-b3f4-17c7c3a89286

-- Sol generated from Applications/EML/EMLDifferentialEquations.lean
import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations
import Theorems.Thm_EMLDiffEq_riccati_ne_of_degree_le
import Theorems.Thm_EMLDiffEq_riccati_ne_of_degree_lt

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



/-- **Kovacic's first case fails for odd-degree coefficients.**

If `r` is a polynomial of odd degree then the Riccati equation `u' + u² = r`
has no solution in the rational function field: there are no polynomials `P`,
`Q` with `Q ≠ 0` satisfying the cleared-denominator identity

  `P'·Q - P·Q' + P² = r·Q²`.

Equivalently, the equation `y'' = r·y` has no solution with rational
logarithmic derivative.  The proof is a degree count: the left-hand side always
has even degree (or too small a degree), while the right-hand side has odd
degree. -/
theorem riccati_no_rational_solution (r P Q : K[X]) (hr : Odd r.natDegree) (hQ : Q ≠ 0) :
    derivative P * Q - P * derivative Q + P ^ 2 ≠ r * Q ^ 2 := by
  have hr0 : r ≠ 0 := ne_zero_of_odd_natDegree hr
  rcases eq_or_ne P 0 with hP | hP
  · intro heq
    rw [hP] at heq
    simp only [map_zero, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at heq
    exact (mul_ne_zero hr0 (pow_ne_zero 2 hQ)) heq.symm
  · rcases Nat.lt_or_ge P.natDegree Q.natDegree with h | h
    · exact riccati_ne_of_degree_lt r P Q hr hP hQ h
    · exact riccati_ne_of_degree_le r P Q hr hP hQ h



/-- Specialisation to the **Airy equation** `y'' = x·y`: the associated Riccati
equation `u' + u² = x` has no rational solution. -/
theorem airy_riccati_no_rational_solution (P Q : K[X]) (hQ : Q ≠ 0) :
    derivative P * Q - P * derivative Q + P ^ 2 ≠ (X : K[X]) * Q ^ 2 := by
  refine riccati_no_rational_solution _ _ _ ?_ hQ
  simp only [Polynomial.natDegree_X]
  exact odd_one



/-! ## 4. From analysis to algebra: Airy has no EML exponential solution -/



/-! ## 5. Sharpness of the odd-degree hypothesis -/





open EMLDiffEq in
theorem solution(P Q : ℝ[X]) (hQ : ∀ x : ℝ, Q.eval x ≠ 0)
    (y : ℝ → ℝ) (hy0 : ∀ x, y x ≠ 0)
    (hy : ∀ x, HasDerivAt y (P.eval x / Q.eval x * y x) x)
    (hy2 : ∀ x, HasDerivAt (fun t => P.eval t / Q.eval t * y t) (x * y x) x) : False := by
  have hQ0 : Q ≠ 0 := by
    intro h; exact hQ 0 (by simp [h])
  have hud : ∀ x : ℝ, HasDerivAt (fun t => P.eval t / Q.eval t)
      (((derivative P).eval x * Q.eval x - P.eval x * (derivative Q).eval x)
        / (Q.eval x) ^ 2) x := fun x => (P.hasDerivAt x).div (Q.hasDerivAt x) (hQ x)
  -- the Riccati identity, pointwise
  have hric : ∀ x : ℝ, x = ((derivative P).eval x * Q.eval x - P.eval x * (derivative Q).eval x)
      / (Q.eval x) ^ 2 + (P.eval x / Q.eval x) ^ 2 := by
    intro x
    have hEq := (hy2 x).unique ((hud x).mul (hy x))
    have h0 : (x - (((derivative P).eval x * Q.eval x - P.eval x * (derivative Q).eval x)
        / (Q.eval x) ^ 2 + (P.eval x / Q.eval x) ^ 2)) * y x = 0 := by
      linear_combination hEq
    have h1 := (mul_eq_zero.mp h0).resolve_right (hy0 x)
    linarith [h1]
  -- clear denominators and pass to a polynomial identity
  have hpoly : ∀ x : ℝ,
      ((derivative P * Q - P * derivative Q + P ^ 2).eval x) = ((X : ℝ[X]) * Q ^ 2).eval x := by
    intro x
    have h := hric x
    have hQx := hQ x
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X]
    field_simp at h
    linarith [h]
  exact airy_riccati_no_rational_solution P Q hQ0 (Polynomial.funext hpoly)
