-- Prove2me | solution 1 for MulAction.stabilizer_fun_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:31.707189+00:00
-- url     : https://prove2.me/submissions/e42a14b5-8b52-49df-9903-4746f4cae091

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace MulAction
theorem _root_.solution {α : Type*} (ι G : Type*) [Nonempty ι] [Group G]
    [MulAction G α] (x : α) :
    MulAction.stabilizer G (fun _ : ι ↦ x) = MulAction.stabilizer G x := by
  ext g
  simp [funext_iff]
end MulAction
