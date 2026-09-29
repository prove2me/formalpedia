-- Prove2me | solution 1 for lean_workbook_plus_22832
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:30.424047+00:00
-- url     : https://prove2.me/submissions/ec29d887-dc7f-4a28-b506-fd80efd9f0bc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b : ℕ} (h : a ∣ b) : 2 ^ a - 1 ∣ 2 ^ b - 1 := by
  intros
  exact Nat.pow_sub_one_dvd_pow_sub_one 2 h
