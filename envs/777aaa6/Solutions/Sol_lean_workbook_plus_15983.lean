-- Prove2me | solution 1 for lean_workbook_plus_15983
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:31.881375+00:00
-- url     : https://prove2.me/submissions/09c271ec-eb79-4d52-8742-47ffdb66807b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y) / z + (y + z) / x + (z + x) / y ≥ 2 * (x + y + z) * (1 / x + 1 / y + 1 / z)) := by
  push_neg
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
  refine ⟨ 1 , ?_⟩
  norm_num at *
  refine ⟨ 2 , ?_⟩
  norm_num at *
