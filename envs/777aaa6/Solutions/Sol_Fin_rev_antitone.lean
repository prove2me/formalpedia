-- Prove2me | solution 1 for Fin.rev_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:06.421772+00:00
-- url     : https://prove2.me/submissions/8bb8d635-3857-4bb4-ab69-a8b85b7182f9

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace Fin
theorem _root_.solution (n : ℕ) : Antitone (Fin.rev (n := n)) := by match n with
  | 0 => intro j; simp
  | n + 1 =>
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      simp only [Fin.rev_le_rev]
      exact Fin.le_of_lt (Fin.castSucc_lt_succ (i := i))
end Fin
