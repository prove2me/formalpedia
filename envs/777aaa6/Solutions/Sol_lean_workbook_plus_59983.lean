-- Prove2me | solution 1 for lean_workbook_plus_59983
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:59.414782+00:00
-- url     : https://prove2.me/submissions/24c64589-424b-4e02-9554-d9e7936016b3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : 2^n > 2017) :
  11 ≤ n := by
  by_contra hn
  have h10 : n ≤ 10 := by omega
  interval_cases n <;> norm_num at h₁
