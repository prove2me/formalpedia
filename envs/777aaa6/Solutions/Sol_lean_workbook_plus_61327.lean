-- Prove2me | solution 1 for lean_workbook_plus_61327
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:51:37.740292+00:00
-- url     : https://prove2.me/submissions/bfe39f52-bf62-424b-bc53-a536aad8e4d1

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

private theorem residue_pow_inverse {p : ℕ} [Fact p.Prime]
    {x : ZMod p} (hx : x ≠ 0) : x ^ (p - 2) = x⁻¹ := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  apply mul_right_cancel₀ hx
  rw [← pow_succ, show p - 2 + 1 = p - 1 by omega,
    ZMod.pow_card_sub_one_eq_one hx, inv_mul_cancel₀ hx]

private theorem small_residue_ne_zero (p m : ℕ) (hm : 0 < m) (hmp : m < p) :
    (m : ZMod p) ≠ 0 := by
  intro hz
  exact (not_le_of_gt hmp) (Nat.le_of_dvd hm ((ZMod.natCast_eq_zero_iff m p).mp hz))

theorem prime_inverse_sum_above_three (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    (2 : ℤ) ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) ≡ 1 [ZMOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := small_residue_ne_zero p 2 (by decide) (by omega)
  have h3 : (3 : ZMod p) ≠ 0 := small_residue_ne_zero p 3 (by decide) hp3
  have h6 : (6 : ZMod p) ≠ 0 := by
    rw [show (6 : ZMod p) = 2 * 3 by norm_num]
    exact mul_ne_zero h2 h3
  have hsum : (2 : ZMod p) ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) = 1 := by
    rw [residue_pow_inverse h2, residue_pow_inverse h3, residue_pow_inverse h6]
    field_simp
    <;> ring
  apply (ZMod.intCast_eq_intCast_iff _ _ p).mp
  simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_one] using hsum

theorem prime_inverse_sum_canonical_residue (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    ((2 : ℤ) ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) ≡
      ((if p = 3 then 2 else 1 : ℕ) : ℤ) [ZMOD p]) ∧
      (if p = 3 then 2 else 1 : ℕ) < p := by
  by_cases hp3 : p = 3
  · subst p
    norm_num [Int.ModEq]
  · have hpgt : 3 < p := by
      have := hp.two_le
      have := Nat.odd_iff.mp hodd
      omega
    simpa only [if_neg hp3, Nat.cast_one] using
      And.intro (prime_inverse_sum_above_three p hp hpgt) (by omega : 1 < p)

theorem solution (p : ℕ) (hp : p.Prime) (hp1 : Odd p) :
    ∃ k : ℕ, (2 ^ (p - 2) + 3 ^ (p - 2) + 6 ^ (p - 2) ≡ k [ZMOD p]) := by
  exact ⟨if p = 3 then 2 else 1, (prime_inverse_sum_canonical_residue p hp hp1).1⟩
