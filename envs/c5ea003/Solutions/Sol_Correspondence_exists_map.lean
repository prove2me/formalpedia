-- Prove2me | solution 1 for Correspondence.exists_map
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:55.386696+00:00
-- url     : https://prove2.me/submissions/32bc255a-17f4-4d1a-b6a7-a402616f1156

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



omit [PseudoMetricSpace α] [PseudoMetricSpace β] in
theorem solution[Nonempty β] {S : Finset α} {T : Finset β} {R : α → β → Prop}
    (hR : IsCorrespondence S T R) :
    ∃ f : α → β, ∀ x ∈ S, f x ∈ T ∧ R x (f x) := by
  haveI : ∀ x : S, Nonempty T := fun ⟨x, hx⟩ => ⟨⟨Classical.choose (hR.1 x hx), (Classical.choose_spec (hR.1 x hx)).1⟩⟩
  let f' : ∀ x : S, T := fun ⟨x, hx⟩ => ⟨Classical.choose (hR.1 x hx), (Classical.choose_spec (hR.1 x hx)).1⟩
  haveI : Inhabited (∀ x : S, T) := ⟨f'⟩
  have key : ∃ f : α → β, ∀ x : S, f x = (f' x).1 := by
    have h : ∀ x : α, ∃ y : β, ∀ hx : x ∈ S, y = (f' ⟨x, hx⟩).1 := fun x => by
      by_cases hx : x ∈ S
      · exact ⟨(f' ⟨x, hx⟩).1, fun _ => rfl⟩
      · exact ⟨Classical.arbitrary β, fun h => (hx h).elim⟩
    use fun x => Classical.choose (h x)
    intro ⟨x, hx⟩
    exact (Classical.choose_spec (h x)) hx
  obtain ⟨f, hf⟩ := key
  use f
  intro x hx
  have hfx : f x = (f' ⟨x, hx⟩).1 := hf ⟨x, hx⟩
  rw [hfx]
  exact ⟨(f' ⟨x, hx⟩).prop, (Classical.choose_spec (hR.1 x hx)).2⟩
