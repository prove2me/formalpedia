-- Prove2me | solution 1 for lean_workbook_plus_55225
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:36:58.070888+00:00
-- url     : https://prove2.me/submissions/d9334ade-fa55-4b71-9a88-6b88b495e3b2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

lemma fifth_power_mod_ten (n : ℤ) : n ^ 5 ≡ n [ZMOD 10] := by
  have h : ∀ a : ZMod 10, a ^ 5 = a := by decide
  apply (ZMod.intCast_eq_intCast_iff (n ^ 5) n 10).mp
  simpa only [Int.cast_pow] using h (n : ZMod 10)

theorem solution : ∀ n : ℕ, n ^ 5 ≡ n [ZMOD 10] := by
  intro n
  simpa only [Nat.cast_pow] using fifth_power_mod_ten (n : ℤ)

#print axioms solution
