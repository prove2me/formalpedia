-- Prove2me | solution 1 for lean_workbook_plus_20728
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:53.253248+00:00
-- url     : https://prove2.me/submissions/6a9f5b48-2e83-4bac-9ce5-3bece8cc05cf

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (k : ℕ) (h₁ : 0 < k) (h₂ : 2 * 2009 ≤ 3 ^ k) : k >= 8 := by
  by_contra h
  have hk : k ≤ 7 := by omega
  interval_cases k <;> norm_num at h₂
