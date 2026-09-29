-- Prove2me | solution 1 for lean_workbook_plus_36924
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:51:05.540686+00:00
-- url     : https://prove2.me/submissions/a8a9c453-355a-4697-932f-1e71d1f76f70

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℕ, 2 ≤ n ∧ n ≤ 9 → 2 ^ n ≤ n ^ 3 := by
  intro n hn
  rcases hn with ⟨h2,h9⟩
  interval_cases n <;> norm_num
