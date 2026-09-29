-- Prove2me | solution 1 for lean_workbook_plus_27718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:20:07.348531+00:00
-- url     : https://prove2.me/submissions/47d22cbe-fe44-4242-ade5-ae97010e7be5

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) (hab : 1 < a) (hbc : 1 < b) (hcd : 1 < c) (hda : 1 < d) : 8 * (a * b * c * d + 1) > (1 + a) * (1 + b) * (1 + c) * (1 + d) := by
  have ha : 0<a-1 := by linarith
  have hb : 0<b-1 := by linarith
  have hc : 0<c-1 := by linarith
  have hd : 0<d-1 := by linarith
  have habp := mul_pos ha hb
  have hacp := mul_nonneg ha.le hc.le
  have hadp := mul_nonneg ha.le hd.le
  have hbcp := mul_nonneg hb.le hc.le
  have hbdp := mul_nonneg hb.le hd.le
  have hcdp := mul_nonneg hc.le hd.le
  have habcp := mul_nonneg habp.le hc.le
  have habdp := mul_nonneg habp.le hd.le
  have hacdp := mul_nonneg hacp hd.le
  have hbcdp := mul_nonneg hbcp hd.le
  have habcdp := mul_nonneg habcp hd.le
  nlinarith only [habp,hacp,hadp,hbcp,hbdp,hcdp,habcp,habdp,hacdp,hbcdp,habcdp]
