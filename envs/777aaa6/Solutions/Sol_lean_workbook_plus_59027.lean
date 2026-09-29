-- Prove2me | solution 1 for lean_workbook_plus_59027
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:16.696558+00:00
-- url     : https://prove2.me/submissions/d8782a62-ff18-40c3-83c4-1592c42dfad4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 4/3 ≤ a) (hb : 4/3 ≤ b) (hc : 4/3 ≤ c) : a + b + c ≥ 8/5 * (2/a - 1/b + 1/c + 1) := by
  have ha0 : 0<a := by linarith
  have hb0 : 0<b := by linarith
  have hc0 : 0<c := by linarith
  have ha1 : 1/a≤3/4 := (div_le_iff₀ ha0).2 (by linarith)
  have hc1 : 1/c≤3/4 := (div_le_iff₀ hc0).2 (by linarith)
  have hb1 : 0≤b-4/3 := by linarith
  have hb2 : 0≤b-6/5 := by linarith
  have hi : b+8/5/b-38/15=(b-4/3)*(b-6/5)/b := by field_simp; ring
  have hp : 0≤(b-4/3)*(b-6/5)/b := by positivity
  have hre : (2/a:ℝ)=2*(1/a) := by ring
  have hrc : (1/b:ℝ)*8/5=8/5/b := by ring
  rw [hre]
  nlinarith only [ha,hc,ha1,hc1,hi,hp,hrc]
