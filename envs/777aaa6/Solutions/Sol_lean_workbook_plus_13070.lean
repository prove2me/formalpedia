-- Prove2me | solution 1 for lean_workbook_plus_13070
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:44:05.999626+00:00
-- url     : https://prove2.me/submissions/38b2a8e4-5a76-44c8-b68b-fd5b1faebb31

import Mathlib

set_option autoImplicit false

namespace FloorFractionalProductLevels

noncomputable section

def value (x : ℝ) : ℝ := x + (⌊x⌋ : ℝ) * Int.fract x

def point (N k : ℤ) : ℝ := ((N : ℝ) + (k : ℝ) ^ 2) / ((k : ℝ) + 1)

theorem negative_value (x : ℝ) (hx : x < 0) : value x < 0 := by
  have hk : (⌊x⌋ : ℝ) ≤ 0 := (Int.floor_le x).trans hx.le
  have ht := Int.fract_nonneg x
  have hp := mul_nonpos_of_nonpos_of_nonneg hk ht
  unfold value
  linarith

theorem nonnegative_of_level (N : ℤ) (hN : 0 ≤ N) (x : ℝ)
    (hx : value x = N) : 0 ≤ x := by
  by_contra h
  have hv := negative_value x (lt_of_not_ge h)
  have hNr : (0 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

theorem floor_band (N : ℤ) (hN : 0 ≤ N) (x : ℝ) (hx : value x = N) :
    ⌊x⌋ ≤ N ∧ N < 2 * ⌊x⌋ + 1 := by
  have hx0 := nonnegative_of_level N hN x hx
  have hk0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx0
  have hk : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast hk0
  have ht0 := Int.fract_nonneg x
  have ht1 := Int.fract_lt_one x
  have hi : value x = (⌊x⌋ : ℝ) + ((⌊x⌋ : ℝ) + 1) * Int.fract x := by
    simp only [value, Int.fract]
    ring
  have hlo := mul_nonneg (by linarith : (0 : ℝ) ≤ (⌊x⌋ : ℝ) + 1) ht0
  have hhi := mul_lt_mul_of_pos_left ht1 (by linarith : (0 : ℝ) < (⌊x⌋ : ℝ) + 1)
  constructor
  · exact_mod_cast (show (⌊x⌋ : ℝ) ≤ N by linarith)
  · exact_mod_cast (show (N : ℝ) < 2 * (⌊x⌋ : ℝ) + 1 by linarith)

theorem point_floor (N k : ℤ) (hN : 0 ≤ N) (hk : k ≤ N) (hNk : N < 2 * k + 1) :
    ⌊point N k⌋ = k := by
  have hk0 : 0 ≤ k := by omega
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have hd : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hlow : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hupp : (N : ℝ) < 2 * (k : ℝ) + 1 := by exact_mod_cast hNk
  apply Int.floor_eq_iff.mpr
  unfold point
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_lt_iff₀ hd).mpr
    nlinarith

theorem point_value (N k : ℤ) (hN : 0 ≤ N) (hk : k ≤ N) (hNk : N < 2 * k + 1) :
    value (point N k) = N := by
  have hf := point_floor N k hN hk hNk
  have hk0 : 0 ≤ k := by omega
  have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk0
  have hd : (k : ℝ) + 1 ≠ 0 := by linarith
  simp only [value, Int.fract]
  rw [hf]
  unfold point
  field_simp
  ring

theorem level_point (N : ℤ) (hN : 0 ≤ N) (x : ℝ) (hx : value x = N) :
    x = point N ⌊x⌋ := by
  have hk0 : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr (nonnegative_of_level N hN x hx)
  have hkr : (0 : ℝ) ≤ ⌊x⌋ := by exact_mod_cast hk0
  have hd : (⌊x⌋ : ℝ) + 1 ≠ 0 := by linarith
  unfold point
  apply (eq_div_iff hd).mpr
  simp only [value, Int.fract] at hx
  nlinarith

theorem level_iff (N : ℤ) (hN : 0 ≤ N) (x : ℝ) :
    value x = N ↔ ∃ k : ℤ, (N + 1) / 2 ≤ k ∧ k ≤ N ∧ x = point N k := by
  constructor
  · intro hx
    obtain ⟨hlo, hhi⟩ := floor_band N hN x hx
    exact ⟨⌊x⌋, by omega, hlo, level_point N hN x hx⟩
  · rintro ⟨k, hlo, hhi, rfl⟩
    exact point_value N k hN hhi (by omega)

def solutions (N : ℤ) : Finset ℝ := by
  classical
  exact (Finset.Icc ((N + 1) / 2) N).image (point N)

theorem mem_solutions (N : ℤ) (hN : 0 ≤ N) (x : ℝ) :
    x ∈ solutions N ↔ value x = N := by
  classical
  simp only [solutions, Finset.mem_image, Finset.mem_Icc]
  rw [level_iff N hN]
  constructor
  · rintro ⟨k, ⟨hlo, hhi⟩, he⟩
    exact ⟨k, hlo, hhi, he.symm⟩
  · rintro ⟨k, hlo, hhi, he⟩
    exact ⟨k, ⟨hlo, hhi⟩, he.symm⟩

theorem point_injective (N : ℤ) (hN : 0 ≤ N) :
    Set.InjOn (point N) (Set.Icc ((N + 1) / 2) N) := by
  intro k hk l hl he
  obtain ⟨hklo, hkhi⟩ := hk
  obtain ⟨hllo, hlhi⟩ := hl
  have hkf := point_floor N k hN hkhi (by omega)
  have hlf := point_floor N l hN hlhi (by omega)
  rw [he] at hkf
  exact hkf.symm.trans hlf

theorem solutions_card (N : ℤ) (hN : 0 ≤ N) :
    (solutions N).card = (N / 2 + 1).toNat := by
  classical
  unfold solutions
  rw [Finset.card_image_of_injOn, Int.card_Icc]
  · congr 1
    omega
  · simpa only [Finset.coe_Icc] using point_injective N hN

theorem finite_level (N : ℤ) (hN : 0 ≤ N) : Set.Finite {x : ℝ | value x = N} := by
  have he : {x : ℝ | value x = N} = (solutions N : Set ℝ) := by
    ext x
    exact (mem_solutions N hN x).symm
  rw [he]
  exact Finset.finite_toSet _

theorem level_ncard (N : ℤ) (hN : 0 ≤ N) :
    Set.ncard {x : ℝ | value x = N} = (N / 2 + 1).toNat := by
  have he : {x : ℝ | value x = N} = (solutions N : Set ℝ) := by
    ext x
    exact (mem_solutions N hN x).symm
  rw [he, Set.ncard_coe_finset, solutions_card N hN]

theorem source_classification (x : ℝ) :
    x + (⌊x⌋ : ℝ) * Int.fract x = 23 ↔
      ∃ k : ℤ, 12 ≤ k ∧ k ≤ 23 ∧ x = (23 + (k : ℝ) ^ 2) / ((k : ℝ) + 1) := by
  simpa only [value, point, show (23 + 1 : ℤ) / 2 = 12 from rfl, Int.cast_ofNat] using
    level_iff 23 (by norm_num) x

theorem source_count : Set.ncard {x : ℝ | x + (⌊x⌋ : ℝ) * Int.fract x = 23} = 12 := by
  simpa [value] using level_ncard 23 (by norm_num)

theorem false_floor_axioms (lf : ℝ → ℤ)
    (hf : ∀ x, (lf x : ℝ) ≤ x) (hf2 : ∀ x, x - (lf x : ℝ) ≤ 0) : False := by
  have h1 := hf (1 / 2)
  have h2 := hf2 (1 / 2)
  have hlow : 0 < lf (1 / 2) := by exact_mod_cast (show (0 : ℝ) < lf (1 / 2) by linarith)
  have hhi : lf (1 / 2) < 1 := by exact_mod_cast (show (lf (1 / 2) : ℝ) < 1 by linarith)
  omega

end

end FloorFractionalProductLevels

theorem solution (lf : ℝ → ℤ) (hf : ∀ x, lf x ≤ x) (hf2 : ∀ x, x - lf x ≤ 0) :
    ∃! x, x + lf x * (x - lf x) = 23 := by
  exact (FloorFractionalProductLevels.false_floor_axioms lf hf hf2).elim

#print axioms FloorFractionalProductLevels.value
#print axioms FloorFractionalProductLevels.point
#print axioms FloorFractionalProductLevels.negative_value
#print axioms FloorFractionalProductLevels.nonnegative_of_level
#print axioms FloorFractionalProductLevels.floor_band
#print axioms FloorFractionalProductLevels.point_floor
#print axioms FloorFractionalProductLevels.point_value
#print axioms FloorFractionalProductLevels.level_point
#print axioms FloorFractionalProductLevels.level_iff
#print axioms FloorFractionalProductLevels.solutions
#print axioms FloorFractionalProductLevels.mem_solutions
#print axioms FloorFractionalProductLevels.point_injective
#print axioms FloorFractionalProductLevels.solutions_card
#print axioms FloorFractionalProductLevels.finite_level
#print axioms FloorFractionalProductLevels.level_ncard
#print axioms FloorFractionalProductLevels.source_classification
#print axioms FloorFractionalProductLevels.source_count
#print axioms FloorFractionalProductLevels.false_floor_axioms
#print axioms solution
