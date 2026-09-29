-- Prove2me | Theorems.Thm_Catalog_Probability_NeuralCoding_Manifold_span_image_le_of_fderiv_const
-- name    : Catalog.Probability.NeuralCoding.Manifold.span_image_le_of_fderiv_const
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:00:09.74949+00:00
-- url     : https://prove2.me/theorems/65068cae-4cac-41ca-bcf4-83a2429536fc
-- title:
--   Affine parametrisations.
-- statement:
--   **Affine parametrisations.**  If the derivative of the behavioural
--   parametrisation is the same linear map `L` at every state, the linear span of the
--   reachable activity has dimension at most `d + 1`: the behavioural degrees of
--   freedom plus one for the offset.
--
--   ```lean
--   theorem Catalog.Probability.NeuralCoding.Manifold.span_image_le_of_fderiv_const(d N : ℕ) (f : (Fin d → ℝ) → (Fin N → ℝ))
--       (L : (Fin d → ℝ) →L[ℝ] (Fin N → ℝ)) (hf : Differentiable ℝ f)
--       (hL : ∀ x, fderiv ℝ f x = L) :
--       finrank ℝ (span ℝ (Set.range f)) ≤ d + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SmoothNeuralManifold.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SmoothNeuralManifold.lean#L51

-- Thm stub generated from Probability/SmoothNeuralManifold.lean
import Mathlib
import Definitions.Def_Probability_SmoothNeuralManifold
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

open Catalog.Probability.NeuralCoding.Manifold

open Module Submodule

theorem Catalog.Probability.NeuralCoding.Manifold.span_image_le_of_fderiv_const(d N : ℕ) (f : (Fin d → ℝ) → (Fin N → ℝ))
    (L : (Fin d → ℝ) →L[ℝ] (Fin N → ℝ)) (hf : Differentiable ℝ f)
    (hL : ∀ x, fderiv ℝ f x = L) :
    finrank ℝ (span ℝ (Set.range f)) ≤ d + 1 := by sorry
