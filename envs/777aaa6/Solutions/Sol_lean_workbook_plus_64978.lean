-- Prove2me | solution 1 for lean_workbook_plus_64978
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:51:05.997849+00:00
-- url     : https://prove2.me/submissions/ebf09c2f-2ec1-42bf-9402-3a30544dc4e5

import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

theorem finite_field_square_trichotomy {F : Type*} [Field F] [Fintype F] (a b : F) :
    IsSquare a ∨ IsSquare b ∨ IsSquare (a * b) := by
  classical
  by_cases ha : IsSquare a
  · exact Or.inl ha
  by_cases hb : IsSquare b
  · exact Or.inr (Or.inl hb)
  right
  right
  by_contra hab
  have h₁ := quadraticChar_neg_one_iff_not_isSquare.mpr ha
  have h₂ := quadraticChar_neg_one_iff_not_isSquare.mpr hb
  have h₃ := quadraticChar_neg_one_iff_not_isSquare.mpr hab
  have hm := map_mul (quadraticChar F) a b
  rw [h₁, h₂, h₃] at hm
  norm_num at hm

theorem intersective_sextic_finite_field {F : Type*} [Field F] [Fintype F] :
    ∃ x : F, x ^ 6 - 11 * x ^ 4 + 36 * x ^ 2 - 36 = 0 := by
  rcases finite_field_square_trichotomy (2 : F) 3 with h | h | h
  all_goals
    rcases (isSquare_iff_exists_sq _).1 h with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    calc
      r ^ 6 - 11 * r ^ 4 + 36 * r ^ 2 - 36 =
          (r ^ 2 - 2) * (r ^ 2 - 3) * (r ^ 2 - 6) := by ring
      _ = 0 := by rw [← hr]; ring

theorem arbitrarily_large_natural_roots (p : ℕ) (hp : p.Prime) (N : ℕ) :
    ∃ x : ℕ, N ≤ x ∧ 4 ≤ x ∧ (x ^ 6 - 11 * x ^ 4 + 36 * x ^ 2 - 36) % p = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := intersective_sextic_finite_field (F := ZMod p)
  let x : ℕ := r.val + p * (N + 4)
  have hg := Nat.mul_le_mul_right (N + 4) hp.one_le
  have hxN : N ≤ x := by dsimp [x]; omega
  have hx4 : 4 ≤ x := by dsimp [x]; omega
  have hxcast : (x : ZMod p) = r := by
    dsimp [x]
    simp
  have hx2 : 11 ≤ x ^ 2 := by nlinarith
  have hfirst : 11 * x ^ 4 ≤ x ^ 6 := by
    calc
      11 * x ^ 4 ≤ x ^ 2 * x ^ 4 := Nat.mul_le_mul_right _ hx2
      _ = x ^ 6 := by ring
  have hsecond : 36 ≤ x ^ 6 - 11 * x ^ 4 + 36 * x ^ 2 := by
    have h := Nat.mul_le_mul_left 36 hx2
    omega
  have hcast : ((x ^ 6 - 11 * x ^ 4 + 36 * x ^ 2 - 36 : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hsecond, Nat.cast_add, Nat.cast_sub hfirst]
    simp only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
    rw [hxcast]
    exact hr
  exact ⟨x, hxN, hx4, Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).1 hcast)⟩

theorem solution (p : ℕ) (hp : p.Prime) :
    ∃ x : ℕ, (x ^ 6 - 11 * x ^ 4 + 36 * x ^ 2 - 36) % p = 0 := by
  obtain ⟨x, _, _, hx⟩ := arbitrarily_large_natural_roots p hp 4
  exact ⟨x, hx⟩
