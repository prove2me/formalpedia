-- Prove2me | solution 1 for lean_workbook_plus_12670
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:30:56.825927+00:00
-- url     : https://prove2.me/submissions/dfe91d25-0760-4b4a-a548-7d9eec2fb1f8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : a ∈ Set.Icc 1 2) (hb : b ∈ Set.Icc 1 2) (hc : c ∈ Set.Icc 1 2) : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + a + b + c := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
