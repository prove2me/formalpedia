-- Prove2me | solution 1 for lean_workbook_plus_57732
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:07:30.150643+00:00
-- url     : https://prove2.me/submissions/2de38695-45d1-4276-9778-516ce89ff8b1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → Real.sqrt x > x := by
  intro x hx
  have hs := Real.sq_sqrt hx.1.le
  have hn := Real.sqrt_nonneg x
  have hm := mul_pos hx.1 (sub_pos.mpr hx.2)
  nlinarith
