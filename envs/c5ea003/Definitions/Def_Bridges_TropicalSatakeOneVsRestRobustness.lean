-- Prove2me | Definitions.Def_Bridges_TropicalSatakeOneVsRestRobustness
-- name    : Bridges_TropicalSatakeOneVsRestRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:03.283497+00:00
-- url     : https://prove2.me/theorems/4238d594-79a1-48b4-8a22-d0d1107a2dae
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakeOneVsRestRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakeOneVsRestRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakeOneVsRestRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.

# GL₃ Tropical Satake One-vs-Rest Certified Robustness

## Overview

This file formalizes a multiclass certified robustness theorem for GL3 tropical
Satake / Hecke-score classifiers under the one-vs-rest decision rule. The key
result shows that the quantitative constant `2 * K * d` from binary score-difference
Lipschitz bounds governs the multiclass certified radius through the one-vs-rest
margin.

## Main Results

* `ovrMargin_le_pair` — the OVR margin is at most each pairwise margin
* `lt_ovrMargin_iff` — characterization of `t < ovrMargin`
* `predicts_of_margin_nonneg` — prediction from nonneg pairwise margins
* `pairwise_nonneg_of_lip_margin` — binary certificate for each class pair
* `gl3_ovr_certified_radius` — main multiclass certified robustness theorem
* `gl3_satake_pairwise_diff_lipschitz` — bridge from per-class Lipschitz to pairwise

## Mathematical Content

The proof reduces multiclass robustness to pairwise margin preservation.
For each competing class `c ≠ y`, the score difference `S y x - S c x` is
bounded by the OVR margin, and the pairwise Lipschitz constant `2 * K * d`
controls the perturbation. The certified radius is `ovrMargin S y x / (2 * K * d)`.
-/


open Finset

noncomputable section

set_option maxHeartbeats 800000

/-! ## Core Definitions -/

/-- The prediction relation: `y` is a maximizer of the score function `S` at `x`. -/
def predicts {C : Type*} {n : ℕ} (S : C → (Fin n → ℝ) → ℝ) (y : C) (x : Fin n → ℝ) : Prop :=
  ∀ c, S c x ≤ S y x

/-- Nonemptiness of `Finset.univ.erase y` for a Nontrivial Fintype. -/
lemma erase_univ_nonempty {C : Type*} [Fintype C] [DecidableEq C] [Nontrivial C] (y : C) :
    (Finset.univ.erase y).Nonempty := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne C
  by_cases hay : a = y
  · exact ⟨b, Finset.mem_erase.mpr ⟨fun h => hab (hay ▸ h.symm), Finset.mem_univ _⟩⟩
  · exact ⟨a, Finset.mem_erase.mpr ⟨hay, Finset.mem_univ _⟩⟩

/-- The one-vs-rest margin at `x` for predicted class `y`:
    the minimum over all competitors `c ≠ y` of `S y x - S c x`. -/
def ovrMargin {C : Type*} [Fintype C] [DecidableEq C] [Nontrivial C]
    {n : ℕ} (S : C → (Fin n → ℝ) → ℝ) (y : C) (x : Fin n → ℝ) : ℝ :=
  (Finset.univ.erase y).inf' (erase_univ_nonempty y) (fun c => S y x - S c x)

/-! ## Margin Lemmas -/



/-! ## Prediction Lemmas -/



/-! ## Binary Certificate Lemma -/

/-
For a single score difference function with Lipschitz bound,
    if the margin is positive and the perturbation is small enough,
    the margin remains nonneg.
-/

/-! ## GL3 Satake Pairwise Difference Lipschitz Bridge -/

/-- A family of score functions indexed by `C` is a GL3 tropical Satake family
    with constants `K` and `d` if each individual score function is `(K * d)`-Lipschitz. -/
structure IsGL3TropicalSatakeFamily {C : Type*} {n : ℕ}
    (S : C → (Fin n → ℝ) → ℝ) (K d : ℝ) : Prop where
  /-- Each score function `S c` is Lipschitz with constant `K * d`. -/
  lip : ∀ c : C, ∀ x z : Fin n → ℝ, |S c x - S c z| ≤ K * d * ‖x - z‖

/-
The pairwise score-difference Lipschitz bound: if each `S c` is `(K*d)`-Lipschitz,
    then the score differences `S a - S b` are `(2*K*d)`-Lipschitz.
    This is the quantitative bridge from the GL3 tropical Satake realization to
    the robustness API.
-/

/-! ## Main Certified Robustness Theorem -/

/-
**GL3 One-vs-Rest Certified Robustness (z-formulation).**

    If `y` is the predicted class at `x` with positive OVR margin,
    and each pairwise score difference `S y - S c` satisfies a
    `(2*K*d)`-Lipschitz bound, then any `z` within the certified radius
    `ovrMargin S y x / (2 * K * d)` preserves the prediction.
-/

/-
**GL3 One-vs-Rest Certified Robustness (δ-formulation).**

    Equivalent to `gl3_ovr_certified_radius'` but stated in terms of
    perturbation `δ` with `z = x + δ`.
-/

/-! ## Corollary: Full GL3 Satake Bridge -/


end


