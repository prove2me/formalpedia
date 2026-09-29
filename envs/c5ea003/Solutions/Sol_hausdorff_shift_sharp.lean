-- Prove2me | solution 1 for hausdorff_shift_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:13.949149+00:00
-- url     : https://prove2.me/submissions/c6a79eeb-5809-4d5f-846f-9260e75f8cfd

-- Sol generated from Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_RipsCorrespondenceInterleaving
/-
  # Correspondence-Based Vietoris–Rips Interleaving

  This file develops, as a chain of results each building on the previous one, the
  *correspondence* version of the Vietoris–Rips scale-translation theorem.

  Background (Phase A thread, Direction 3): a matched sample `x_i ↦ y_i` with
  `dist (x i) (y i) ≤ δ` translates Rips scales by exactly `2δ`. Indexwise matching
  is only a special case of a *correspondence*: a relation `R ⊆ X × Y` surjective on
  both factors. The right invariant of a correspondence is its **distortion**
  `sup |dist x x' - dist y y'|` over related pairs, and it is the distortion — not the
  matching — that governs the scale translation.

  ## The chain

  1. `IsRipsSimplex_mono` — Rips complexes are monotone in the scale.
  2. `Correspondence.exists_map` — every correspondence contains a *choice map*.
  3. `Correspondence.dist_map_le` — a choice map distorts distances by at most `c`.
  4. `Correspondence.image_isRipsSimplex` — hence pushes `ε`-simplices to `(ε+c)`-simplices.
  5. `Correspondence.symm` + `Correspondence.image_isRipsSimplex'` — the reverse direction,
     giving a two-sided `c`-interleaving of the Rips filtrations.
  6. `Correspondence.roundTrip_close` — the round trip `g ∘ f` moves points by at most `c`.
  7. `Correspondence.union_roundTrip_isRipsSimplex` — hence `g ∘ f` is contiguous to the
     identity inside the `(ε+2c)`-Rips complex (the simplicial ingredient that makes the
     interleaving descend to homology).
  8. `Correspondence.comp_distortionLe` — distortions add under composition, so the
     interleavings compose.
  9. `matched_distortionLe` and `matched_image_isRipsSimplex` — the classical matched-sample
     `2δ` translation is the special case of an indexwise correspondence, whose distortion
     is at most `2δ`.
  10. `hausdorff_distortionLe`, `hausdorff_image_isRipsSimplex`, `hausdorff_shift_sharp` —
      two samples at Hausdorff distance `≤ δ` in a common space are related by the
      `δ`-closeness correspondence, whose distortion is at most `2δ`; the resulting `2δ`
      scale translation is sharp.
  11. `interleaving_shift_sharp` — sharpness: for every `c > 0` and every shift `η < c`
      there is a correspondence of distortion `≤ c` between two-point and one-point subsets
      of `ℝ` for which the shift `η` fails. Hence the constant `c` (i.e. `2δ` in the matched
      case, by 9) cannot be improved.
-/

open Finset

noncomputable section

variable {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]

/-! ## Part 1: Rips simplices of a finite subset -/




/-! ## Part 2: Correspondences between finite samples -/





/-! ## Part 3: The interleaving -/







/-! ## Part 4: Composition of correspondences -/



/-! ## Part 5: Matched samples are the special case of distortion `2δ` -/





/-! ## Part 5b: Hausdorff-close samples -/






/-! ## Part 6: Sharpness of the shift -/



theorem solution{δ : ℝ} (hδ : 0 < δ) :
    HausdorffLe ({0, 2 * δ} : Finset ℝ) ({δ} : Finset ℝ) δ ∧
      IsRipsSimplex ({δ} : Finset ℝ) 0 {δ} ∧
      (∀ x ∈ ({0, 2 * δ} : Finset ℝ), dist x δ ≤ δ) ∧
      dist (0 : ℝ) (2 * δ) = 2 * δ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- HausdorffLe {0, 2δ} {δ} δ
    simp [HausdorffLe, Real.dist_eq]
    exact ⟨⟨le_of_eq (abs_of_pos hδ), by rw [show 2 * δ - δ = δ by ring, abs_of_pos hδ]⟩, Or.inl (le_of_eq (abs_of_pos hδ))⟩
  · -- IsRipsSimplex {δ} 0 {δ}
    simp [IsRipsSimplex]
  · -- ∀ x ∈ {0, 2δ}, dist x δ ≤ δ
    intro x hx
    simp at hx ⊢
    rcases hx with rfl | rfl
    · rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos hδ]
    · rw [Real.dist_eq, show 2 * δ - δ = δ by ring, abs_of_pos hδ]
  · -- dist 0 (2 * δ) = 2 * δ
    rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 * δ)]
