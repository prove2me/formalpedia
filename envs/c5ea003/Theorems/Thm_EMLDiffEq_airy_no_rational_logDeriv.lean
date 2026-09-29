-- Prove2me | Theorems.Thm_EMLDiffEq_airy_no_rational_logDeriv
-- name    : EMLDiffEq.airy_no_rational_logDeriv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:46:34.75882+00:00
-- url     : https://prove2.me/theorems/61fc2180-4cbb-4dba-8c55-2f970a1b803d
-- title:
--   **No nowhere-vanishing solution of the Airy equation has a rational
-- statement:
--   **No nowhere-vanishing solution of the Airy equation has a rational
--   logarithmic derivative.**
--
--   Here `y` is a nowhere-vanishing function whose logarithmic derivative is the
--   rational function `P/Q` (with `Q` nowhere vanishing) and which satisfies
--   `y'' = x·y`.  Such a `y` cannot exist.
--
--   ```lean
--   theorem EMLDiffEq.airy_no_rational_logDeriv(P Q : ℝ[X]) (hQ : ∀ x : ℝ, Q.eval x ≠ 0)
--       (y : ℝ → ℝ) (hy0 : ∀ x, y x ≠ 0)
--       (hy : ∀ x, HasDerivAt y (P.eval x / Q.eval x * y x) x)
--       (hy2 : ∀ x, HasDerivAt (fun t => P.eval t / Q.eval t * y t) (x * y x) x) : False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/EMLDifferentialEquations.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/EMLDifferentialEquations.lean#L357

-- Thm stub generated from Applications/EML/EMLDifferentialEquations.lean
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

theorem EMLDiffEq.airy_no_rational_logDeriv(P Q : ℝ[X]) (hQ : ∀ x : ℝ, Q.eval x ≠ 0)
    (y : ℝ → ℝ) (hy0 : ∀ x, y x ≠ 0)
    (hy : ∀ x, HasDerivAt y (P.eval x / Q.eval x * y x) x)
    (hy2 : ∀ x, HasDerivAt (fun t => P.eval t / Q.eval t * y t) (x * y x) x) : False := by sorry
