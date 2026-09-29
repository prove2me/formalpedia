-- Prove2me | solution 1 for lean_workbook_plus_24237
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:54:52.047904+00:00
-- url     : https://prove2.me/submissions/ca29e614-0db6-409b-afe7-181548745f44

import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (R : Type*) [Ring R] [Finite R] (x : R) : ∃ n : ℕ, n • x = 0 := by
  have hn : 0 < Nat.card R := Nat.card_pos
  exact ⟨Nat.card R, card_nsmul_eq_zero'⟩
