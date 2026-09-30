-- Prove2me | solution 1 for lean_workbook_plus_52634
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:41.212577+00:00
-- url     : https://prove2.me/submissions/c0e03908-d19a-40b2-a473-94025ebd65c4

import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Finite.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

theorem square_roots_one_mod_2019_iff (y : ℤ) :
    y ^ 2 ≡ 1 [ZMOD 2019] ↔
      y % 2019 = 1 ∨ y % 2019 = 674 ∨ y % 2019 = 1345 ∨ y % 2019 = 2018 := by
  have hp3 : Prime (3 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have hp673 : Prime (673 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have hfactor : y ^ 2 - 1 = (y - 1) * (y + 1) := by ring
  calc
    y ^ 2 ≡ 1 [ZMOD 2019] ↔ (2019 : ℤ) ∣ y ^ 2 - 1 := by
      rw [Int.modEq_iff_dvd]
      omega
    _ ↔ (3 : ℤ) ∣ y ^ 2 - 1 ∧ (673 : ℤ) ∣ y ^ 2 - 1 := by omega
    _ ↔ ((3 : ℤ) ∣ y - 1 ∨ (3 : ℤ) ∣ y + 1) ∧
        ((673 : ℤ) ∣ y - 1 ∨ (673 : ℤ) ∣ y + 1) := by
      rw [hfactor, hp3.dvd_mul, hp673.dvd_mul]
    _ ↔ y % 2019 = 1 ∨ y % 2019 = 674 ∨ y % 2019 = 1345 ∨ y % 2019 = 2018 := by
      omega

theorem affine_square_2019_classification (x y : ℤ) :
    2019 * x + 1 = y ^ 2 ↔
      (y % 2019 = 1 ∨ y % 2019 = 674 ∨ y % 2019 = 1345 ∨ y % 2019 = 2018) ∧
      x = (y ^ 2 - 1) / 2019 := by
  constructor
  · intro h
    have hmul : 2019 * x = y ^ 2 - 1 := by omega
    have hroot : y ^ 2 ≡ 1 [ZMOD 2019] := by
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-x, by omega⟩
    exact ⟨(square_roots_one_mod_2019_iff y).mp hroot,
      Int.eq_ediv_of_mul_eq_right (by decide) hmul⟩
  · rintro ⟨hr, hx⟩
    have hroot := (square_roots_one_mod_2019_iff y).mpr hr
    have hd : (2019 : ℤ) ∣ y ^ 2 - 1 := by
      have hh := hroot.dvd
      omega
    have hm := Int.mul_ediv_cancel_of_dvd hd
    rw [← hx] at hm
    omega

theorem affine_square_2019_positive_solutions_infinite :
    {y : ℤ | 0 < y ∧ ∃ x : ℤ, 0 < x ∧ 2019 * x + 1 = y ^ 2}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => 2019 * ((n : ℤ) + 1) + 1)
  · intro a b h
    change 2019 * ((a : ℤ) + 1) + 1 = 2019 * ((b : ℤ) + 1) + 1 at h
    omega
  · intro n
    have hn : 0 < (n : ℤ) + 1 := by omega
    refine ⟨by omega, 2019 * ((n : ℤ) + 1) ^ 2 + 2 * ((n : ℤ) + 1), ?_, ?_⟩
    · positivity
    · ring

theorem solution : ¬ (¬ (∃ x y : ℤ, 2019 * x + 1 = y ^ 2)) := by
  intro h
  have hw : 2019 * (2021 : ℤ) + 1 = (2020 : ℤ) ^ 2 :=
    (affine_square_2019_classification 2021 2020).mpr (by norm_num)
  exact h ⟨2021, 2020, hw⟩
