-- Prove2me | Theorems.Thm_EMLDiffEq_riccati_ne_of_degree_lt
-- name    : EMLDiffEq.riccati_ne_of_degree_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:46:31.35954+00:00
-- url     : https://prove2.me/theorems/540b955a-7c1d-4330-863c-8b5d59e06ec4
-- title:
--   Branch `deg P < deg Q` of `riccati_no_rational_solution`: here the whole
-- statement:
--   Branch `deg P < deg Q` of `riccati_no_rational_solution`: here the whole
--   left-hand side has degree `< 2 · deg Q`, which is smaller than the degree of the
--   right-hand side.
--
--   ```lean
--   theorem EMLDiffEq.riccati_ne_of_degree_lt(r P Q : K[X]) (hr : Odd r.natDegree) (hP : P ≠ 0) (hQ : Q ≠ 0)
--       (hlt : P.natDegree < Q.natDegree) :
--       derivative P * Q - P * derivative Q + P ^ 2 ≠ r * Q ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/EML/EMLDifferentialEquations.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/EML/EMLDifferentialEquations.lean#L236

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

theorem EMLDiffEq.riccati_ne_of_degree_lt(r P Q : K[X]) (hr : Odd r.natDegree) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hlt : P.natDegree < Q.natDegree) :
    derivative P * Q - P * derivative Q + P ^ 2 ≠ r * Q ^ 2 := by sorry
