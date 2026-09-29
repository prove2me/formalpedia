-- Prove2me | solution 1 for ThreeCubes.card_repsBox_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:29:09.513475+00:00
-- url     : https://prove2.me/submissions/034f1fe1-05a8-47ff-89f0-04e462813a62

-- Sol generated from Probability/Counting.lean
import Mathlib
import Definitions.Def_Probability_Basic
import Definitions.Def_Probability_Counting
import Theorems.Thm_ThreeCubes_mahler_one_injective
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
    2 * T + 1 ≤ (repsBox 1 (12 * (T : ℤ) ^ 4 + 9 * (T : ℤ) ^ 3 + 3 * (T : ℤ) + 1)).card := by
  set B : ℤ := 12 * (T : ℤ) ^ 4 + 9 * (T : ℤ) ^ 3 + 3 * (T : ℤ) + 1 with hB
  set f : ℤ → ℤ × ℤ × ℤ := fun t => (9 * t ^ 4, 3 * t - 9 * t ^ 4, 1 - 9 * t ^ 3) with hf
  have hsub : (Finset.Icc (-(T : ℤ)) T).image f ⊆ repsBox 1 B := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    rw [Finset.mem_Icc] at ht
    have habs : |t| ≤ (T : ℤ) := abs_le.mpr ht
    obtain ⟨b4, b3, b3', -, -, -⟩ := pow_bounds habs
    have hT0 : (0 : ℤ) ≤ (T : ℤ) := Int.natCast_nonneg T
    have hT3 : (0 : ℤ) ≤ (T : ℤ) ^ 3 := by positivity
    have hT4 : (0 : ℤ) ≤ (T : ℤ) ^ 4 := by positivity
    have ht4 : (0 : ℤ) ≤ t ^ 4 := by positivity
    simp only [repsBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, hf, hB]
    refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩,
      ⟨by linarith, by linarith⟩⟩, by ring⟩
  have hinj : Set.InjOn f (Finset.Icc (-(T : ℤ)) T) := by
    intro a _ b _ hab
    exact mahler_one_injective hab
  calc 2 * T + 1 = (Finset.Icc (-(T : ℤ)) T).card := (card_Icc_neg T).symm
    _ = ((Finset.Icc (-(T : ℤ)) T).image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ _ := Finset.card_le_card hsub
