-- Prove2me | solution 1 for Correspondence.union_roundTrip_isRipsSimplex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:56.366119+00:00
-- url     : https://prove2.me/submissions/b36a0417-24d0-44db-b548-f7b7c7b63bca

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




/-- A choice map of a correspondence of distortion `≤ c` increases distances by at most `c`. -/
theorem Correspondence.dist_map_le {S : Finset α} {T : Finset β} {R : α → β → Prop}
    {c : ℝ} (hc : DistortionLe S T R c) {f : α → β} (hf : ∀ x ∈ S, f x ∈ T ∧ R x (f x))
    {x x' : α} (hx : x ∈ S) (hx' : x' ∈ S) :
    dist (f x) (f x') ≤ dist x x' + c := by
  have hfx : f x ∈ T ∧ R x (f x) := hf x hx
  have hfx' : f x' ∈ T ∧ R x' (f x') := hf x' hx'
  have h := hc x hx (f x) hfx.1 x' hx' (f x') hfx'.1 hfx.2 hfx'.2
  linarith [abs_le.mp h]

/-! ## Part 3: The interleaving -/



/-- The transpose of a correspondence has the same distortion bound. -/
theorem Correspondence.distortionLe_symm {S : Finset α} {T : Finset β} {R : α → β → Prop}
    {c : ℝ} (hc : DistortionLe S T R c) :
    DistortionLe T S (fun y x => R x y) c := by
  intro y hy x hx y' hy' x' hx' hxy hxy'
  rw [abs_sub_comm]
  exact hc x hx y hy x' hx' y' hy' hxy hxy'


/-- **Round trip.** The composite `g ∘ f` of two choice maps moves each sample point of `S`
    by at most the distortion `c`. -/
theorem Correspondence.roundTrip_close {S : Finset α} {T : Finset β} {R : α → β → Prop}
    {c : ℝ} (hc : DistortionLe S T R c) {f : α → β} (hf : ∀ x ∈ S, f x ∈ T ∧ R x (f x))
    {g : β → α} (hg : ∀ y ∈ T, g y ∈ S ∧ R (g y) y) {x : α} (hx : x ∈ S) :
    dist x (g (f x)) ≤ c := by
  have hfxT : f x ∈ T := (hf x hx).1
  have hfR : R x (f x) := (hf x hx).2
  have hgfxS : g (f x) ∈ S := (hg (f x) hfxT).1
  have hgR : R (g (f x)) (f x) := (hg (f x) hfxT).2
  have h := hc x hx (f x) hfxT (g (f x)) hgfxS (f x) hfxT hfR hgR
  simp at h
  linarith


/-! ## Part 4: Composition of correspondences -/



/-! ## Part 5: Matched samples are the special case of distortion `2δ` -/





/-! ## Part 5b: Hausdorff-close samples -/






/-! ## Part 6: Sharpness of the shift -/



theorem solution{S : Finset α} {T : Finset β}
    {R : α → β → Prop} {c ε : ℝ} (hc₀ : 0 ≤ c) (hc : DistortionLe S T R c)
    {f : α → β} (hf : ∀ x ∈ S, f x ∈ T ∧ R x (f x))
    {g : β → α} (hg : ∀ y ∈ T, g y ∈ S ∧ R (g y) y)
    [DecidableEq α] {s : Finset α} (hs : IsRipsSimplex S ε s) :
    IsRipsSimplex S (ε + 2 * c) (s ∪ s.image (g ∘ f)) := by
  -- For g, use the symmetric correspondence
  have hc' : DistortionLe T S (fun y x => R x y) c := Correspondence.distortionLe_symm hc
  have hg' : ∀ y ∈ T, g y ∈ S ∧ (fun y x => R x y) y (g y) := fun y hy => (hg y hy)
  refine ⟨?_, ?_⟩
  · -- Subset: s ∪ s.image (g ∘ f) ⊆ S
    apply Finset.union_subset hs.1
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (hg (f y) (hf y (hs.1 hy)).1).1
  · -- Distance bound
    intro x hx y hy
    simp only [Finset.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · -- Both in s
      exact le_add_of_le_of_nonneg (hs.2 x hx y hy) (by linarith)
    · -- x ∈ s, y ∈ s.image (g ∘ f)
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hzS : z ∈ S := hs.1 hz
      have h1 : dist z (g (f z)) ≤ c := Correspondence.roundTrip_close hc hf hg hzS
      have h2 : dist x z ≤ ε := hs.2 x hx z hz
      calc dist x (g (f z)) ≤ dist x z + dist z (g (f z)) := dist_triangle _ _ _
        _ ≤ ε + c := add_le_add h2 h1
        _ ≤ ε + 2 * c := by linarith
    · -- x ∈ s.image (g ∘ f), y ∈ s
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hyS : y ∈ S := hs.1 hy
      have hzS : z ∈ S := hs.1 hz
      have h1 : dist z (g (f z)) ≤ c := Correspondence.roundTrip_close hc hf hg hzS
      have h2 : dist z y ≤ ε := hs.2 z hz y hy
      calc dist (g (f z)) y ≤ dist (g (f z)) z + dist z y := dist_triangle _ _ _
        _ = dist z (g (f z)) + dist z y := by rw [dist_comm]
        _ ≤ c + ε := add_le_add h1 h2
        _ ≤ ε + 2 * c := by linarith
    · -- Both in s.image (g ∘ f)
      obtain ⟨u, hu, hu'⟩ := Finset.mem_image.mp hx
      obtain ⟨v, hv, hv'⟩ := Finset.mem_image.mp hy
      rw [← hu', ← hv']
      have huS : u ∈ S := hs.1 hu
      have hvS : v ∈ S := hs.1 hv
      have hfu : f u ∈ T := (hf u huS).1
      have hfv : f v ∈ T := (hf v hvS).1
      have h1 : dist (f u) (f v) ≤ dist u v + c := Correspondence.dist_map_le hc hf huS hvS
      have h2 : dist (g (f u)) (g (f v)) ≤ dist (f u) (f v) + c :=
        Correspondence.dist_map_le hc' hg' hfu hfv
      calc dist (g (f u)) (g (f v)) ≤ dist (f u) (f v) + c := h2
        _ ≤ dist u v + c + c := by linarith
        _ = dist u v + 2 * c := by ring
        _ ≤ ε + 2 * c := add_le_add_left (hs.2 u hu v hv) _
