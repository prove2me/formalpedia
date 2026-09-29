-- Prove2me | solution 1 for lean_workbook_plus_27984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:22.204891+00:00
-- url     : https://prove2.me/submissions/e33d5ccd-1c3b-4778-998a-167570979ae3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n m : ℕ)
  (h₀ : n > m)
  (h₁ : 0 < m) :
  2 * (n^2 - 2 * n * m + m^2 - n + m) = 2 * n^2 - 4 * n * m + 2 * m^2 - 2 * n + 2 * m := by
  intros
  grind
