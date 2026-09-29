-- Prove2me | solution 1 for lean_workbook_plus_77848
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:42:44.753541+00:00
-- url     : https://prove2.me/submissions/f95a3424-2037-4884-ae17-18e54dc47d3b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (1900 ^ 1990 - 1 ≡ 0 [ZMOD 1991]) := by
  have hp0 : (1900 : ℤ)^1 ≡ 1900 [ZMOD 1991] := by norm_num [Int.ModEq]
  have hp1 : (1900 : ℤ)^3 ≡ 1018 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (1 : ℕ)*2+1=3 by decide] using ((hp0.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (1900 : ℤ)^2*1900 ≡ 1018 [ZMOD 1991])
  have hp2 : (1900 : ℤ)^7 ≡ 222 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (3 : ℕ)*2+1=7 by decide] using ((hp1.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (1018 : ℤ)^2*1900 ≡ 222 [ZMOD 1991])
  have hp3 : (1900 : ℤ)^15 ≡ 879 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (7 : ℕ)*2+1=15 by decide] using ((hp2.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (222 : ℤ)^2*1900 ≡ 879 [ZMOD 1991])
  have hp4 : (1900 : ℤ)^31 ≡ 1834 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (15 : ℕ)*2+1=31 by decide] using ((hp3.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (879 : ℤ)^2*1900 ≡ 1834 [ZMOD 1991])
  have hp5 : (1900 : ℤ)^62 ≡ 757 [ZMOD 1991] := by
    simpa only [← pow_mul,show (31 : ℕ)*2=62 by decide] using (hp4.pow 2).trans (by norm_num [Int.ModEq] : (1834 : ℤ)^2 ≡ 757 [ZMOD 1991])
  have hp6 : (1900 : ℤ)^124 ≡ 1632 [ZMOD 1991] := by
    simpa only [← pow_mul,show (62 : ℕ)*2=124 by decide] using (hp5.pow 2).trans (by norm_num [Int.ModEq] : (757 : ℤ)^2 ≡ 1632 [ZMOD 1991])
  have hp7 : (1900 : ℤ)^248 ≡ 1457 [ZMOD 1991] := by
    simpa only [← pow_mul,show (124 : ℕ)*2=248 by decide] using (hp6.pow 2).trans (by norm_num [Int.ModEq] : (1632 : ℤ)^2 ≡ 1457 [ZMOD 1991])
  have hp8 : (1900 : ℤ)^497 ≡ 1498 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (248 : ℕ)*2+1=497 by decide] using ((hp7.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (1457 : ℤ)^2*1900 ≡ 1498 [ZMOD 1991])
  have hp9 : (1900 : ℤ)^995 ≡ 560 [ZMOD 1991] := by
    simpa only [← pow_mul,← pow_succ,show (497 : ℕ)*2+1=995 by decide] using ((hp8.pow 2).mul (Int.ModEq.refl 1900)).trans (by norm_num [Int.ModEq] : (1498 : ℤ)^2*1900 ≡ 560 [ZMOD 1991])
  have hp10 : (1900 : ℤ)^1990 ≡ 1013 [ZMOD 1991] := by
    simpa only [← pow_mul,show (995 : ℕ)*2=1990 by decide] using (hp9.pow 2).trans (by norm_num [Int.ModEq] : (560 : ℤ)^2 ≡ 1013 [ZMOD 1991])
  have hp : (1900 : ℤ)^1990%1991=1013 := by
    simpa only [Int.ModEq,show (1013 : ℤ)%1991=1013 by decide] using hp10
  intro h
  change ((1900 : ℤ)^1990-1)%1991=0%1991 at h
  rw [Int.sub_emod,hp] at h
  norm_num at h
