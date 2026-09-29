-- Prove2me | solution 1 for lean_workbook_plus_22691
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:10.571178+00:00
-- url     : https://prove2.me/submissions/5b8e08e6-4f72-49e4-8003-31571658a02e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {d n : ℕ} (h : d ∣ n) : 2 ^ d - 1 ∣ 2 ^ n - 1 := by
  intros
  exact?
