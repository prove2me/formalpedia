-- Prove2me | solution 1 for lean_workbook_plus_30518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:31.430161+00:00
-- url     : https://prove2.me/submissions/506cf716-c63b-4c4a-9639-ceaf01048dba

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℕ → ℕ) (h : ∀ n, a n = n) : ∀ n, a (2 * n) = a n + n := by
  intros
  grind
