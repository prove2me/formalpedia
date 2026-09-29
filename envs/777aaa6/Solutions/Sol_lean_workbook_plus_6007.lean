-- Prove2me | solution 1 for lean_workbook_plus_6007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:26.927615+00:00
-- url     : https://prove2.me/submissions/4336f46c-0304-4243-9a29-dc4c1c5b88ca

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℕ)
  (n : ℕ)
  (h₀ : n = x + 19) :
  n * (n + 1) * (n + 2) * (n + 3) = (n^2 + 3 * n + 1)^2 - 1 := by
  intros
  grind
