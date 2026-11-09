-- Prove2me | solution 1 for Couret.STROBO2TORS.NontranslationCollision.ne
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:13.012523+00:00
-- url     : https://prove2.me/submissions/adc524d8-22b4-4637-a67e-0de1b251cba5

import Aesop
import Definitions.Def_Couret_Strobo2TorsPairCount_5c76f0dc12bb
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]
































attribute [local instance] Classical.propDecidable











omit [Fintype G] in
theorem NontranslationCollision.p2m_local_ne {S T : Finset G} (h : NontranslationCollision S T) : S ≠ T := by
  intro heq
  apply h.2.2.2.2.2
  exact ⟨0,by simpa [translateSupport] using heq.symm⟩

















end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  {S T : Finset.{p2m_u_0} G},
  @Couret.STROBO2TORS.NontranslationCollision.{p2m_u_0} G inst inst_1 S T → @Ne.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) S T := @_root_.Couret.STROBO2TORS.NontranslationCollision.p2m_local_ne

