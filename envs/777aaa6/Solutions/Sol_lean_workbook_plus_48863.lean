-- Prove2me | solution 1 for lean_workbook_plus_48863
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:53:59.642533+00:00
-- url     : https://prove2.me/submissions/d00bdede-d2bd-4c41-be9c-e962dffbd5ce

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ¬ ∃ l, ∀ n, |(-1 : ℝ)^n - l| < 1 := by
  rintro ⟨l,h⟩
  have h0 := h 0
  have h1 := h 1
  clear h
  norm_num at h0 h1
  have ha := abs_lt.mp h0
  have hb := abs_lt.mp h1
  grind
