-- Prove2me | solution 1 for EMLDiffEq.EMLExpr.firstOrder_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:57:51.948521+00:00
-- url     : https://prove2.me/submissions/6d07f3d4-f7fa-4997-bc19-73df0025d617

-- Sol generated from Applications/EML/EMLDifferentialEquations.lean
import Mathlib
import Definitions.Def_Applications_EML_EMLDifferentialEquations
import Theorems.Thm_EMLDiffEq_EMLExpr_hasDerivAt_eval

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





open EMLDiffEq.EMLExpr in
theorem solution(F : EMLExpr) (hF : ∀ x, Regular F x)
    (y : ℝ → ℝ) (hy : ∀ x, HasDerivAt y (eval (D F) x * y x) x) :
    ∃ K : ℝ, ∀ x, y x = K * Real.exp (eval F x) := by
  set g : ℝ → ℝ := fun t => y t * Real.exp (-(eval F t)) with hg
  have hgd : ∀ x, HasDerivAt g 0 x := by
    intro x
    have h1 : HasDerivAt (fun t => Real.exp (-(eval F t)))
        (-(eval (D F) x) * Real.exp (-(eval F x))) x := by
      have := ((hasDerivAt_eval F x (hF x)).neg).exp
      simpa [mul_comm] using this
    show HasDerivAt (fun t => y t * Real.exp (-(eval F t))) 0 x
    convert (hy x).mul h1 using 1
    ring
  have hconst : ∀ x, g x = g 0 :=
    fun x => is_const_of_deriv_eq_zero (fun t => (hgd t).differentiableAt)
      (fun t => (hgd t).deriv) x 0
  refine ⟨g 0, fun x => ?_⟩
  have hx := hconst x
  have h2 : y x * Real.exp (-(eval F x)) * Real.exp (eval F x) = g 0 * Real.exp (eval F x) := by
    rw [← hx]
  rw [mul_assoc, ← Real.exp_add] at h2
  simpa using h2
