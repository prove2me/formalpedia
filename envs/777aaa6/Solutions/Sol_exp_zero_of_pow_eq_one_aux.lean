-- Prove2me | solution 1 for exp_zero_of_pow_eq_one_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:00.389109+00:00
-- url     : https://prove2.me/submissions/f9de8388-47af-4df3-8fca-ef1765dd866e

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
theorem _root_.solution {n : ℕ} (ha : (0 : Γ₀) ^ n = 1) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n _ => simp at ha
