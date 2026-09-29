-- Prove2me | solution 1 for lean_workbook_plus_31211
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:36.49422+00:00
-- url     : https://prove2.me/submissions/d18b84c0-c201-4398-b5e9-e601b91f3d3d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) : ∃ k, 2 ^ k ≥ n := by
  exact ⟨n,(Nat.lt_two_pow_self (n:=n)).le⟩
