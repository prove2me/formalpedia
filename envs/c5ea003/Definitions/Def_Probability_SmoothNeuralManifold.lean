-- Prove2me | Definitions.Def_Probability_SmoothNeuralManifold
-- name    : Probability_SmoothNeuralManifold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:36:09.65108+00:00
-- url     : https://prove2.me/theorems/2fd69840-ae93-4a45-9401-8d6c5fe83ca9
-- title:
--   Aether Catalog definitions — Probability_SmoothNeuralManifold
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.SmoothNeuralManifold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/SmoothNeuralManifold.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The neural manifold hypothesis for smooth behavioural parametrisations

`Catalog/Novelty/NeuralCoding.lean` proves `neural_manifold_dim_le_dof`: if the
population activity in `ℝ^N` is driven **linearly** by `d` behavioural degrees of
freedom, the reachable activity spans at most `d` dimensions.  Neural
parametrisations are however smooth, not linear, and this file settles what
survives.

Three different numbers must be distinguished for a smooth
`f : ℝ^d → ℝ^N`:

* the **tangent rank** at a point, `finrank (range (fderiv ℝ f x))`;
* the dimension of the **linear span** of the image, `finrank (span ℝ (range f))`;
* the (topological) dimension of the image itself.

## Results

1. `tangent_rank_le_dof` — **the local rank bound.**  The tangent rank of a
   smooth behavioural parametrisation is at most `d` at every point; this is the
   correct smooth generalisation of the linear theorem.
2. `span_image_le_of_fderiv_const` — if the derivative is *constant* (the affine
   case) the span of the image has dimension at most `d + 1`, the extra
   dimension coming from the offset.
3. `exists_smooth_span_gt_dof` — **the linear theorem does not extend to spans.**
   There is a `C^∞` curve (`d = 1`) in `ℝ²` whose image spans a `2`-dimensional
   subspace.  So a low-dimensional behavioural parametrisation does *not* bound
   the linear dimension of the recorded activity; only the tangent rank is
   controlled.
-/

namespace Catalog.Probability.NeuralCoding.Manifold

open Module Submodule



/-- The moment curve `t ↦ (t, t²)`, a smooth one-parameter behavioural
parametrisation of activity in `ℝ²`. -/
noncomputable def momentCurve : ℝ → (Fin 2 → ℝ) := fun t i => t ^ (i.val + 1)



end Catalog.Probability.NeuralCoding.Manifold


