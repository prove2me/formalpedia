-- Prove2me | solution 1 for MulAction.stabilizer_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:31.066487+00:00
-- url     : https://prove2.me/submissions/e7daa2ec-dd20-4f55-86c1-2b82b0e445e9

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
namespace MulAction
theorem _root_.solution {ι : Type*} {α : ι → Type*} (G : Type*) [Group G]
    [∀ i, MulAction G (α i)] (x : ∀ i, α i) :
    MulAction.stabilizer G x = ⨅ i, MulAction.stabilizer G (x i) := by
  ext g
  simp [funext_iff, Subgroup.mem_iInf]
end MulAction
