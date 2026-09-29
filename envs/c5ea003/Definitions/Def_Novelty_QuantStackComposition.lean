-- Prove2me | Definitions.Def_Novelty_QuantStackComposition
-- name    : Novelty_QuantStackComposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:38:43.335615+00:00
-- url     : https://prove2.me/theorems/f0341eed-7f87-4ea2-a5b1-3e630fdff440
-- title:
--   Aether Catalog definitions — Novelty_QuantStackComposition
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.QuantStackComposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/QuantStackComposition.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor

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

namespace Catalog.Novelty.QuantStack

open Finset Catalog.Novelty.QuantCurvature

variable {n : ℕ}

/-- The Hessian-metric pairing of two perturbations. -/
noncomputable def quadPair (lam e f : Fin n → ℝ) : ℝ := (1 / 2) * ∑ i, lam i * (e i * f i)








end Catalog.Novelty.QuantStack


