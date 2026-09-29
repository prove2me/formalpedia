-- Prove2me | solution 1 for ThreeCubes.card_repsBox_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:34:54.560997+00:00
-- url     : https://prove2.me/submissions/54a462ce-a351-4a69-848d-02d4477757d7

-- Sol generated from Probability/Counting.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Counting
import Theorems.Thm_ThreeCubes_family_two_injective
import Theorems.Thm_ThreeCubes_pow_bounds

/-!
# Counting representations: `1` and `2` are exceptional

Heath-Brown's conjecture predicts that for a *generic* admissible `n` the number of
representations `n = x³ + y³ + z³` with `max(|x|,|y|,|z|) ≤ B` grows like `c_n log B`.  The
integers `1` and `2` are famously exceptional: the classical one-parameter families give
`≫ B^{1/4}` and `≫ B^{1/3}` representations respectively, which is vastly more than
logarithmic.

This file makes those lower bounds explicit and formal:

* `ThreeCubes.card_repsBox_one` : at least `2T+1` representations of `1` inside the box of
  radius `12T⁴ + 9T³ + 3T + 1`, i.e. `≫ B^{1/4}` representations of height `≤ B`;
* `ThreeCubes.card_repsBox_two` : at least `2T+1` representations of `2` inside the box of
  radius `6T³ + 6T² + 1`, i.e. `≫ B^{1/3}` representations of height `≤ B`.
-/

open ThreeCubes


theorem card_Icc_neg (T : ℕ) : (Finset.Icc (-(T : ℤ)) T).card = 2 * T + 1 := by
  rw [Int.card_Icc]; omega






open ThreeCubes in
theorem solution(T : ℕ) :
    2 * T + 1 ≤ (repsBox 2 (6 * (T : ℤ) ^ 3 + 6 * (T : ℤ) ^ 2 + 1)).card := by
  set B : ℤ := 6 * (T : ℤ) ^ 3 + 6 * (T : ℤ) ^ 2 + 1 with hB
  set g : ℤ → ℤ × ℤ × ℤ := fun t => (1 + 6 * t ^ 3, 1 - 6 * t ^ 3, -6 * t ^ 2) with hg
  have hsub : (Finset.Icc (-(T : ℤ)) T).image g ⊆ repsBox 2 B := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    rw [Finset.mem_Icc] at ht
    have habs : |t| ≤ (T : ℤ) := abs_le.mpr ht
    obtain ⟨-, b3, b3', b2, -, -⟩ := pow_bounds habs
    have hT2 : (0 : ℤ) ≤ (T : ℤ) ^ 2 := by positivity
    have hT3 : (0 : ℤ) ≤ (T : ℤ) ^ 3 := by positivity
    have ht2 : (0 : ℤ) ≤ t ^ 2 := by positivity
    simp only [repsBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, hg, hB]
    refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩⟩, by ring⟩
  have hinj : Set.InjOn g (Finset.Icc (-(T : ℤ)) T) := by
    intro a _ b _ hab
    exact family_two_injective hab
  calc 2 * T + 1 = (Finset.Icc (-(T : ℤ)) T).card := (card_Icc_neg T).symm
    _ = ((Finset.Icc (-(T : ℤ)) T).image g).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
