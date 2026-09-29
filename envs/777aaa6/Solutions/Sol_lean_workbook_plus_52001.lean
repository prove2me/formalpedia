-- Prove2me | solution 1 for lean_workbook_plus_52001
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:27.353588+00:00
-- url     : https://prove2.me/submissions/b49fde01-a243-4b96-b3a8-a8f6996a81d6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ¬ ∃ (x : ℚ), ↑x = Real.sqrt 2 := by
  rintro ⟨q,hq⟩
  exact irrational_sqrt_two ⟨q,hq⟩
