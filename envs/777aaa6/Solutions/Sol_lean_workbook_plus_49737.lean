-- Prove2me | solution 1 for lean_workbook_plus_49737
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:33.432744+00:00
-- url     : https://prove2.me/submissions/1a3b7ef4-555f-4cf6-ab88-ad59374fc5df

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ {d n : ℕ}, d ∣ n → (2 ^ d - 1) ∣ (2 ^ n - 1) := by
  intros
  exact?
