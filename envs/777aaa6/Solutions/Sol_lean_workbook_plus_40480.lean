-- Prove2me | solution 1 for lean_workbook_plus_40480
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:21.639758+00:00
-- url     : https://prove2.me/submissions/df1468d2-e7ad-446c-ba4f-fe70938168ed

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution (a b : ℝ) (h : a > b) : ∃ n : ℕ, a > b + 1 / n := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < a-b by linarith)
  refine ⟨n+1, ?_⟩
  push_cast
  linarith
