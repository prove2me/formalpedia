-- Prove2me | solution 1 for lean_workbook_plus_65865
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:45:53.74331+00:00
-- url     : https://prove2.me/submissions/3560dd54-6c80-45ea-9f24-9b47e9334dfe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  Finset.card (Finset.filter (λ x => ¬ 2∣x ∧ ¬ 3∣x) (Finset.Icc 2 999)) = 332 := by
  intros
  rfl
