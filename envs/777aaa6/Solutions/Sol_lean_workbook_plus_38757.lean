-- Prove2me | solution 1 for lean_workbook_plus_38757
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:13.225182+00:00
-- url     : https://prove2.me/submissions/9614cc52-9e35-450a-9f83-1c070c722def

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {y n : ℕ} (h : y ∣ n) : 2 ^ y - 1 ∣ 2 ^ n - 1 := by
  intros
  exact?
