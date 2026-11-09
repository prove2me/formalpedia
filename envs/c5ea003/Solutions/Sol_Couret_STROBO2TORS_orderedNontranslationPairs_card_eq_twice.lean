-- Prove2me | solution 1 for Couret.STROBO2TORS.orderedNontranslationPairs_card_eq_twice
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:12.338326+00:00
-- url     : https://prove2.me/submissions/89211c2e-0f84-4b1c-a840-45176e8feff2

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
import Theorems.Thm_Couret_STROBO2TORS_nontranslationPairs_preimage
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

















theorem p2m_local_orderedNontranslationPairs_card_eq_twice :
    (orderedNontranslationPairs : Finset (Finset G × Finset G)).card =
      2 * (nontranslationPairs : Finset (Finset (Finset G))).card := by
  calc
    _ = ∑ P ∈ (nontranslationPairs : Finset (Finset (Finset G))),
        ((orderedNontranslationPairs : Finset (Finset G × Finset G)).filter
          (fun p => ({p.1,p.2} : Finset (Finset G))=P)).card :=
      Finset.card_eq_sum_card_image _ _
    _ = ∑ _P ∈ (nontranslationPairs : Finset (Finset (Finset G))), 2 := by
      apply Finset.sum_congr rfl
      exact nontranslationPairs_preimage
    _ = _ := by simp [Nat.mul_comm]











end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{1} Nat
    (@Finset.card.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
        (@Couret.STROBO2TORS.nontranslationPairs.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_orderedNontranslationPairs_card_eq_twice

