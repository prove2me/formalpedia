-- Prove2me | solution 1 for lean_workbook_plus_21992
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:39.453574+00:00
-- url     : https://prove2.me/submissions/be3b1cc7-7048-4ea4-b3bb-c9a5d8e7fd26

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ n : ℕ, (⌊Real.sqrt n + 1⌋ ^ 2) ≥ n + 1 := by
  intro n
  rw [Int.floor_add_one,Real.floor_real_sqrt_eq_nat_sqrt]
  have h := Nat.lt_succ_sqrt' n
  exact_mod_cast h
