-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Manifold.exists_smooth_span_gt_dof
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:46:58.331101+00:00
-- url     : https://prove2.me/submissions/4c84c91d-54ec-40ed-aa2a-360bb911b05e

-- Sol generated from Probability/SmoothNeuralManifold.lean
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




theorem contDiff_momentCurve : ContDiff ℝ (⊤ : ℕ∞) momentCurve := by
  rw [contDiff_pi]
  intro i
  exact contDiff_id.pow _



open Catalog.Probability.NeuralCoding.Manifold in
theorem solution:
    ∃ f : ℝ → (Fin 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) f ∧
      1 < finrank ℝ (span ℝ (Set.range f)) := by
  refine ⟨momentCurve, contDiff_momentCurve, ?_⟩
  have hli : LinearIndependent ℝ ![momentCurve 1, momentCurve 2] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrFun hst 0
    have h1 := congrFun hst 1
    simp only [momentCurve, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h0 h1
    norm_num at h0 h1
    constructor <;> linarith
  have hcard : finrank ℝ (span ℝ (Set.range ![momentCurve 1, momentCurve 2])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  have hsub : span ℝ (Set.range ![momentCurve 1, momentCurve 2]) ≤
      span ℝ (Set.range momentCurve) := by
    apply span_le.mpr
    rintro y ⟨i, rfl⟩
    fin_cases i
    · exact subset_span ⟨1, rfl⟩
    · exact subset_span ⟨2, rfl⟩
  have := Submodule.finrank_mono hsub
  omega
