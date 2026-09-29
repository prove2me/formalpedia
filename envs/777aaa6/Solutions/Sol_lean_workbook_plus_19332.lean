-- Prove2me | solution 1 for lean_workbook_plus_19332
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:42.058887+00:00
-- url     : https://prove2.me/submissions/2e7327d0-06ad-4134-b45d-c1b73a71acf6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (hn : 3 ≤ n) : (n - 1) ^ 2 > 2 := by
  have h2 : 2≤n-1 := by omega
  nlinarith
