-- Prove2me | Definitions.Def_Bridges_GraphTheory_RipsCorrespondenceInterleaving
-- name    : Bridges_GraphTheory_RipsCorrespondenceInterleaving
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:23:23.899378+00:00
-- url     : https://prove2.me/theorems/024d6f9e-7927-4bee-8b3e-ff5b316b1b9d
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_RipsCorrespondenceInterleaving
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.RipsCorrespondenceInterleaving`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean by skeleton subtraction
import Mathlib
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

/-- `s` is a simplex of the Vietoris–Rips complex of the finite sample `S` at scale `ε`:
    it is a subset of `S` of diameter at most `ε`. -/
def IsRipsSimplex (S : Finset α) (ε : ℝ) (s : Finset α) : Prop :=
  s ⊆ S ∧ ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε



/-! ## Part 2: Correspondences between finite samples -/

/-- `R` is a correspondence between the samples `S` and `T`: every point of `S` is related
    to some point of `T` and conversely. -/
def IsCorrespondence (S : Finset α) (T : Finset β) (R : α → β → Prop) : Prop :=
  (∀ x ∈ S, ∃ y ∈ T, R x y) ∧ (∀ y ∈ T, ∃ x ∈ S, R x y)

/-- The correspondence `R` has distortion at most `c`: related pairs have distances
    agreeing up to `c`. -/
def DistortionLe (S : Finset α) (T : Finset β) (R : α → β → Prop) (c : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ T, ∀ x' ∈ S, ∀ y' ∈ T, R x y → R x' y' → |dist x x' - dist y y'| ≤ c



/-! ## Part 3: The interleaving -/







/-! ## Part 4: Composition of correspondences -/



/-! ## Part 5: Matched samples are the special case of distortion `2δ` -/

/-- The indexwise correspondence attached to a matched pair of samples: `x` is related to `y`
    when they are the images of a common index. -/
def matchedRel {ι : Type*} (X Y : ι → α) : α → α → Prop :=
  fun x y => ∃ i : ι, X i = x ∧ Y i = y




/-! ## Part 5b: Hausdorff-close samples -/

/-- Two finite samples of a common metric space are at Hausdorff distance at most `δ`. -/
def HausdorffLe (S T : Finset α) (δ : ℝ) : Prop :=
  (∀ x ∈ S, ∃ y ∈ T, dist x y ≤ δ) ∧ (∀ y ∈ T, ∃ x ∈ S, dist x y ≤ δ)





/-! ## Part 6: Sharpness of the shift -/


end


