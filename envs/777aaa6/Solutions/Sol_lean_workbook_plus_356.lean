-- Prove2me | solution 1 for lean_workbook_plus_356
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:41.645546+00:00
-- url     : https://prove2.me/submissions/a62f31a4-3c0a-42ea-957d-940a69b58348

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n x a : ℝ)
  (h₀ : n = 2)
  (h₁ : a = (9 - 2 * n) / (6 * n))
  (h₂ : x = n + a) :
  x = 29 / 12 := by
  intros
  grind
