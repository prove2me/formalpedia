-- Prove2me | solution 1 for lean_workbook_plus_18973
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:13.396267+00:00
-- url     : https://prove2.me/submissions/b8a4cf2b-cd6c-4002-93e7-4a228a15bf1f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q : ℤ) (h₁ : (p : ℝ)^2 - 4 * q = (abs p - 2)^2) : q = abs p - 1 := by
  have hs : ((abs p:ℤ):ℝ)^2=(p:ℝ)^2 := by norm_cast; exact sq_abs p
  have he : (q:ℝ)=((abs p:ℤ):ℝ)-1 := by nlinarith
  exact_mod_cast he
