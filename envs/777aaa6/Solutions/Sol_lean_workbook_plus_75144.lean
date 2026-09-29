-- Prove2me | solution 1 for lean_workbook_plus_75144
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:57.510932+00:00
-- url     : https://prove2.me/submissions/23653824-31db-48eb-ae13-f3633e45278c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ)
  (h₀ : 7 * 15 ≤ n)
  (h₁ : n ≤ 7 * 142) :
  Finset.card (Finset.filter (λ x => 7∣x) (Finset.Icc 100 999)) = 128 := by
  intros
  rfl
