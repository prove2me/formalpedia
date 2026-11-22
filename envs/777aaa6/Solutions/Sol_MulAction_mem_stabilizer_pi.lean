-- Prove2me | solution 1 for MulAction.mem_stabilizer_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:41.010177+00:00
-- url     : https://prove2.me/submissions/ca5644cf-2037-4df0-b957-0f007888f1e7

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace MulAction
theorem _root_.solution {ι : Type*} {α : ι → Type*} {G : Type*} [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) (g : G) :
    g ∈ MulAction.stabilizer G x ↔ ∀ i, g ∈ MulAction.stabilizer G (x i) := by
  simp [funext_iff, Subgroup.mem_iInf]
end MulAction
