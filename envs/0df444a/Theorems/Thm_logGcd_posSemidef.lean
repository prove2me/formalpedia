-- Prove2me | Theorems.Thm_logGcd_posSemidef
-- name    : logGcd_posSemidef
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:11:25.834313+00:00
-- url     : https://prove2.me/theorems/2b23cf28-08a7-4139-ae4a-bc8aa3bb36fb
-- title:
--   log Gcd pos Semidef: log Gcd pos Semidef
-- statement:
--   The log Gcd pos Semidef construction uses the log Gcd pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/irregular-rhomboid/log-gcd-lean/blob/170787f66795b7d732a29922244638df9ec737da/Loggcd/Lean/loggcd.lean#L25-L90
-- source:
--   https://github.com/irregular-rhomboid/log-gcd-lean/blob/170787f66795b7d732a29922244638df9ec737da/Loggcd/Lean/loggcd.lean#L25-L90

import Mathlib
import Definitions.Def_Loggcd_Lean_loggcd
set_option autoImplicit true
open Finset ArithmeticFunction
variable {ι : Type*} [Fintype ι]

theorem logGcd_posSemidef
    (x : ι → ℕ) (hx : ∀ i, 1 ≤ x i) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * Real.log (Nat.gcd (x i) (x j)) := by sorry
