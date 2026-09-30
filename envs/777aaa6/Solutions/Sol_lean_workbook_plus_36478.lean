-- Prove2me | solution 1 for lean_workbook_plus_36478
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:30:51.253672+00:00
-- url     : https://prove2.me/submissions/ff4fa806-4e5c-48a4-a074-8fdcd928680b

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem even_odd_quadratic_permutation (A B C k : ℕ) (hA : Even A) (hB : Odd B) :
    Function.Bijective (fun x : ZMod (2 ^ k) => A * x ^ 2 + B * x + C) := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  have hinj : Function.Injective (fun x : ZMod (2 ^ k) => A * x ^ 2 + B * x + C) := by
    intro x y hxy
    have hodd : Odd (A * (x.val + y.val) + B) := by
      apply Nat.odd_iff.mpr
      simp [Nat.add_mod, Nat.mul_mod, Nat.even_iff.mp hA, Nat.odd_iff.mp hB]
    have hcop := hodd.coprime_two_right.pow_right k
    have hu := (ZMod.isUnit_iff_coprime (A * (x.val + y.val) + B) (2 ^ k)).mpr hcop
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at hu
    apply sub_eq_zero.mp
    apply hu.mul_left_eq_zero.mp
    calc
      (x - y) * ((A : ZMod (2 ^ k)) * (x + y) + B) =
          (A * x ^ 2 + B * x + C) - (A * y ^ 2 + B * y + C) := by ring
      _ = 0 := sub_eq_zero.mpr hxy
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

theorem two_adic_unique_quadratic_root (A B C k : ℕ) (hA : Even A) (hB : Odd B) :
    ∃! x : ZMod (2 ^ k), A * x ^ 2 + B * x + C = 0 := by
  have hbij := even_odd_quadratic_permutation A B C k hA hB
  obtain ⟨x, hx⟩ := hbij.2 0
  exact ⟨x, hx, fun y hy => hbij.1 (hy.trans hx.symm)⟩

theorem arbitrarily_large_two_adic_quadratic_roots (A B C k L : ℕ)
    (hA : Even A) (hB : Odd B) :
    ∃ m : ℕ, L < m ∧ 2 ^ k ∣ A * m ^ 2 + B * m + C := by
  letI : NeZero (2 ^ k) := ⟨pow_ne_zero _ (by decide)⟩
  obtain ⟨r, hr, _⟩ := two_adic_unique_quadratic_root A B C k hA hB
  let m := r.val + 2 ^ k * (L + 1)
  have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  have hmul : L + 1 ≤ 2 ^ k * (L + 1) := by
    have h1 : 1 ≤ 2 ^ k := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right (L + 1) h1
  have hcast : (m : ZMod (2 ^ k)) = r := by
    simp only [m, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
      ZMod.natCast_self, zero_mul, add_zero]
  refine ⟨m, by dsimp [m]; omega, ?_⟩
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hcast] using hr

theorem two_adic_quadratic_lift_choice (A B C k m : ℕ) (hA : Even A) (hB : Odd B)
    (hm : 2 ^ k ∣ A * m ^ 2 + B * m + C) :
    (2 ^ (k + 1) ∣ A * m ^ 2 + B * m + C) ↔
      ¬ (2 ^ (k + 1) ∣ A * (m + 2 ^ k) ^ 2 + B * (m + 2 ^ k) + C) := by
  obtain ⟨q, hq⟩ := hm
  have hshift : A * (m + 2 ^ k) ^ 2 + B * (m + 2 ^ k) + C =
      2 ^ k * (q + 2 * A * m + A * 2 ^ k + B) := by
    calc
      _ = (A * m ^ 2 + B * m + C) + 2 ^ k * (2 * A * m + A * 2 ^ k + B) := by
        ring
      _ = _ := by rw [hq]; ring
  have hp : 0 < (2 : ℕ) ^ k := pow_pos (by decide) _
  rw [pow_succ, hq, hshift, Nat.mul_dvd_mul_iff_left hp, Nat.mul_dvd_mul_iff_left hp]
  have hmod : (q + 2 * A * m + A * 2 ^ k + B) % 2 = (q + 1) % 2 := by
    simp [Nat.add_mod, Nat.mul_mod, Nat.even_iff.mp hA, Nat.odd_iff.mp hB]
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hmod]
  omega

theorem solution : ¬ (∀ m k : ℕ,
    (2018 * (m + 2 ^ k) ^ 2 + 20182017 * (m + 2 ^ k) + 2017) % (2 ^ (k + 1)) = 0) := by
  intro h
  have hbad := h 0 1
  norm_num at hbad
