-- Prove2me | solution 1 for lean_workbook_plus_76406
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:37:43.989436+00:00
-- url     : https://prove2.me/submissions/8e850012-e296-4881-8b74-54b620ddbc92

import Mathlib

set_option autoImplicit false

theorem residue_equivalence (z : ZMod 7) : z ^ 10 = 1 ↔ z ^ 2 = 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : z ^ 7 = z := ZMod.pow_card z
  have h20 : z ^ 20 = z ^ 2 := by
    calc
      z ^ 20 = z ^ 7 * z ^ 13 := by ring
      _ = z * z ^ 13 := by rw [h7]
      _ = (z ^ 7) ^ 2 := by ring
      _ = z ^ 2 := by rw [h7]
  constructor
  · intro h
    calc
      z ^ 2 = z ^ 20 := h20.symm
      _ = (z ^ 10) ^ 2 := by ring
      _ = 1 := by rw [h]; norm_num
  · intro h
    calc
      z ^ 10 = (z ^ 2) ^ 5 := by ring
      _ = 1 := by rw [h]; norm_num

theorem solution (x : Nat) : x ^ 10 ≡ 1 [ZMOD 7] ↔ x ^ 2 ≡ 1 [ZMOD 7] := by
  have h10 : ((x : ZMod 7) ^ 10 = 1) ↔ (x : Int) ^ 10 ≡ 1 [ZMOD 7] := by
    have h := ZMod.intCast_eq_intCast_iff ((x : Int) ^ 10) 1 7
    rw [Int.cast_pow, Int.cast_natCast, Int.cast_one] at h
    exact h
  have h2 : ((x : ZMod 7) ^ 2 = 1) ↔ (x : Int) ^ 2 ≡ 1 [ZMOD 7] := by
    have h := ZMod.intCast_eq_intCast_iff ((x : Int) ^ 2) 1 7
    rw [Int.cast_pow, Int.cast_natCast, Int.cast_one] at h
    exact h
  exact h10.symm.trans ((residue_equivalence (x : ZMod 7)).trans h2)

#print axioms solution
