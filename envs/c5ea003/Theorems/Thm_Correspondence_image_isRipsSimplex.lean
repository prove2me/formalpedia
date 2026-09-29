-- Prove2me | Theorems.Thm_Correspondence_image_isRipsSimplex
-- name    : Correspondence.image_isRipsSimplex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:41:48.934924+00:00
-- url     : https://prove2.me/theorems/38c0c7d0-c6e3-46d8-9319-5d3b4317ce19
-- title:
--   Interleaving, forward direction.
-- statement:
--   **Interleaving, forward direction.** A choice map of a correspondence of distortion
--       at most `c` sends `ε`-Rips simplices of `S` to `(ε + c)`-Rips simplices of `T`.
--
--   ```lean
--   theorem Correspondence.image_isRipsSimplex{S : Finset α} {T : Finset β} {R : α → β → Prop}
--       {c ε : ℝ} (hc : DistortionLe S T R c) {f : α → β} (hf : ∀ x ∈ S, f x ∈ T ∧ R x (f x))
--       [DecidableEq β] {s : Finset α} (hs : IsRipsSimplex S ε s) :
--       IsRipsSimplex T (ε + c) (s.image f) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean#L116

-- Thm stub generated from Bridges/GraphTheory/RipsCorrespondenceInterleaving.lean
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

theorem Correspondence.image_isRipsSimplex{S : Finset α} {T : Finset β} {R : α → β → Prop}
    {c ε : ℝ} (hc : DistortionLe S T R c) {f : α → β} (hf : ∀ x ∈ S, f x ∈ T ∧ R x (f x))
    [DecidableEq β] {s : Finset α} (hs : IsRipsSimplex S ε s) :
    IsRipsSimplex T (ε + c) (s.image f) := by sorry
