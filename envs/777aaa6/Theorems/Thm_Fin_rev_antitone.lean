-- Prove2me | Theorems.Thm_Fin_rev_antitone
-- name    : Fin.rev_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:45:42.725412+00:00
-- url     : https://prove2.me/theorems/9b40fc47-9691-4388-9c3e-36c6ae25b75a
-- title:
--   Fin: rev antitone
-- statement:
--   The Fin construction uses the rev antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L90-L96
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean#L90-L96

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc
set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem Fin.rev_antitone (n : ℕ) : Antitone (Fin.rev (n := n)) := by sorry
