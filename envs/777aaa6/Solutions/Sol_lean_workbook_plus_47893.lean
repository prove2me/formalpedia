-- Prove2me | solution 1 for lean_workbook_plus_47893
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:27.78781+00:00
-- url     : https://prove2.me/submissions/0701623c-6f07-42eb-af74-9b88f93ec1d9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1) : a * (1 - b) + b * (1 - c) + c * (1 - d) + d * (1 - a) ≤ 2 := by
  intros
  nlinarith
