-- Prove2me | solution 1 for lean_workbook_plus_17718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:41.90188+00:00
-- url     : https://prove2.me/submissions/46a148de-ff2b-4bcf-ab2f-da6be766ca9e

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℕ)
  (h₀ : x^3 ≡ y^3 [MOD 10]) :
  x ≡ y [MOD 10] := by
  have hc (z : ℕ) : (z^3)^3 ≡ z [MOD 10] := by
    have hr : ((z%10)^3)^3 ≡ z%10 [MOD 10] := by
      have hz := Nat.mod_lt z (by decide : 0 < 10)
      interval_cases h : z % 10 <;> norm_num [Nat.ModEq]
    have hm := Nat.mod_modEq z 10
    exact ((hm.pow 3).pow 3).symm.trans (hr.trans hm)
  exact (hc x).symm.trans ((h₀.pow 3).trans (hc y))
