-- Prove2me | solution 1 for lean_workbook_plus_32057
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:26:57.413623+00:00
-- url     : https://prove2.me/submissions/2ec52d48-1205-414d-bc40-3a4130ce2364

import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ t : ℝ, t > 0 → ((t + 2) / (t + 1) ≥ 3 - (3 * t) / 2)) := by
  push_neg
  norm_num at *
  refine ⟨ (    1  /  2  ) , ?_⟩
  norm_num at *
