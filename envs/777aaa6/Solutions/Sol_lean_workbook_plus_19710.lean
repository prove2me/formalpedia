-- Prove2me | solution 1 for lean_workbook_plus_19710
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:53.964054+00:00
-- url     : https://prove2.me/submissions/c9c2e425-dd9a-427c-9687-190fa1292f3b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : { n : ℕ | n ≤ 40 ∧ n % 4 = 2 } = { 2, 6, 10, 14, 18, 22, 26, 30, 34, 38 } := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega
