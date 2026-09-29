-- Prove2me | solution 1 for hausdorff_distortionLe
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:15:13.373033+00:00
-- url     : https://prove2.me/submissions/dc6db0f5-766c-4a8c-9269-11375de0ae89

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



theorem solution(S T : Finset α) (δ : ℝ) :
    DistortionLe S T (fun x y => dist x y ≤ δ) (2 * δ) := by
  intro x hx y hy x' hx' y' hy' hxy hxy'
  have h1 : dist x x' ≤ dist x y + dist y y' + dist y' x' := by
    calc dist x x' ≤ dist x y + dist y x' := dist_triangle _ _ _
      _ ≤ dist x y + dist y y' + dist y' x' := by linarith [dist_triangle y y' x']
  have h2 : dist y y' ≤ dist y x + dist x x' + dist x' y' := by
    calc dist y y' ≤ dist y x + dist x y' := dist_triangle _ _ _
      _ ≤ dist y x + dist x x' + dist x' y' := by linarith [dist_triangle x x' y']
  have hdist_comm : dist y' x' = dist x' y' := dist_comm _ _
  have hdist_comm' : dist y x = dist x y := dist_comm _ _
  rw [hdist_comm] at h1
  rw [hdist_comm'] at h2
  have h3 : dist x x' ≤ dist y y' + 2 * δ := by linarith
  have h4 : dist y y' ≤ dist x x' + 2 * δ := by linarith
  rw [abs_le]
  constructor <;> linarith
