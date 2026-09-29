-- Prove2me | Theorems.Thm_Catalog_Novelty_QuantStack_quadExcess_add_le
-- name    : Catalog.Novelty.QuantStack.quadExcess_add_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:16:30.437647+00:00
-- url     : https://prove2.me/theorems/5546cae3-97d6-4b85-9e64-125697b0f1d6
-- title:
--   The triangle inequality for quantisation cost.
-- statement:
--   **The triangle inequality for quantisation cost.**  `√Q` is a seminorm in the
--   perturbation, so the excess of a composed stack is at most the square of the sum
--   of the individual square-root costs.
--
--   ```lean
--   theorem Catalog.Novelty.QuantStack.quadExcess_add_le(lam e f : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
--       quadExcess lam (e + f)
--         ≤ (Real.sqrt (quadExcess lam e) + Real.sqrt (quadExcess lam f)) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/QuantStackComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/QuantStackComposition.lean#L74

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

theorem Catalog.Novelty.QuantStack.quadExcess_add_le(lam e f : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    quadExcess lam (e + f)
      ≤ (Real.sqrt (quadExcess lam e) + Real.sqrt (quadExcess lam f)) ^ 2 := by sorry
