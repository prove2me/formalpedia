-- Prove2me | solution 1 for lean_workbook_plus_38104
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:17:44.855568+00:00
-- url     : https://prove2.me/submissions/a636500b-7416-4812-9412-a0e2a405b03a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : 7 ∣ 1^2015 + 2^2015 + 3^2015 + 4^2015 + 5^2015 + 6^2015 := by
  have general : ∀ n:ℕ,Odd n → 7 ∣ (1:ℕ)^n+2^n+3^n+4^n+5^n+6^n := by
    intro n hn
    have h1 : (6:ℤ)^n ≡ -1 [ZMOD 7] := by
      have h := (show (6:ℤ) ≡ -1 [ZMOD 7] by norm_num [Int.ModEq]).pow n
      simpa only [hn.neg_pow,one_pow] using h
    have h2 : (5:ℤ)^n ≡ -(2:ℤ)^n [ZMOD 7] := by
      have h := (show (5:ℤ) ≡ -2 [ZMOD 7] by norm_num [Int.ModEq]).pow n
      simpa only [hn.neg_pow] using h
    have h3 : (4:ℤ)^n ≡ -(3:ℤ)^n [ZMOD 7] := by
      have h := (show (4:ℤ) ≡ -3 [ZMOD 7] by norm_num [Int.ModEq]).pow n
      simpa only [hn.neg_pow] using h
    have hh := (((Int.ModEq.rfl (n:=7) (a:=1)).add (Int.ModEq.rfl (a:=(2:ℤ)^n))).add (Int.ModEq.rfl (a:=(3:ℤ)^n))).add h3 |>.add h2 |>.add h1
    have he : (7:ℤ) ∣ 1+2^n+3^n+4^n+5^n+6^n := by
      apply Int.modEq_zero_iff_dvd.mp
      convert hh using 1 <;> ring
    simp only [one_pow]
    exact_mod_cast he
  exact general 2015 (by decide)
