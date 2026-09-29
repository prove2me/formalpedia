-- Prove2me | Theorems.Thm_Catalog_Novelty_QuantStack_quadPair_sq_le
-- name    : Catalog.Novelty.QuantStack.quadPair_sq_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:16:25.493724+00:00
-- url     : https://prove2.me/theorems/6cce6855-eecc-4520-badc-19c63ee8938e
-- title:
--   Cauchy–Schwarz in the Hessian metric.
-- statement:
--   **Cauchy–Schwarz in the Hessian metric.**  Valid for a positive
--   *semi*definite Hessian: eigenvalues are only assumed nonnegative.
--
--   ```lean
--   theorem Catalog.Novelty.QuantStack.quadPair_sq_le(lam e f : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
--       quadPair lam e f ^ 2 ≤ quadExcess lam e * quadExcess lam f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/QuantStackComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/QuantStackComposition.lean#L50

-- Thm stub generated from Novelty/QuantStackComposition.lean
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor
import Definitions.Def_Novelty_QuantStackComposition

/-!
# Composing quantisation axes: the serving-stack budget is a seminorm

Cycle 2 of the NET-95 thread.  The practical claim attached to the measurement is
that a CPU serving stack composes independent compressions — `q4_k_m` weights
(+1.816%) with a K8/V4 cache (+0.14%) — and that the aggregate cost is "about the
sum".  This file proves what the curvature model actually licenses, which is
strictly stronger and quantitative.

In the second-order model of `Novelty.QuantCurvatureNoFloor`, the excess loss
`quadExcess lam e = ½ ∑ᵢ λᵢ eᵢ²` is the *square of a seminorm* in the
perturbation `e`.  Consequently:

* `quadExcess_sqrt_subadditive` / `quadExcess_add_le` — the triangle inequality:
  `√Q(e + f) ≤ √Q(e) + √Q(f)`.  Costs add in the square-root scale, never worse.
  (Proved from the discrete Cauchy–Schwarz inequality applied to the vectors
  `√λᵢ eᵢ` and `√λᵢ fᵢ`; degeneracy `λᵢ = 0` is allowed.)
* `stack_excess_le` — hence a two-axis budget: `Q ≤ a + b + 2√(ab)`.
* `cpu_stack_aggregate_bound` — instantiated at the measured numbers, the whole
  weight + cache stack is guaranteed to cost **under 3%** of perplexity, whatever
  the correlation between the two perturbations.
* `stack_excess_additive_of_orthogonal` — and if the two perturbations are
  orthogonal in the Hessian metric (the "independent noise" hypothesis), the cost
  is *exactly* additive.  With the measured numbers this predicts
  `1.816% + 0.14% = 1.956%`, versus the worst-case `2.97%`: a sharp, falsifiable
  prediction for the joint weight × cache arm that has not yet been run.
-/

open Catalog.Novelty.QuantStack

open Finset Catalog.Novelty.QuantCurvature

variable {n : ℕ}

theorem Catalog.Novelty.QuantStack.quadPair_sq_le(lam e f : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    quadPair lam e f ^ 2 ≤ quadExcess lam e * quadExcess lam f := by sorry
