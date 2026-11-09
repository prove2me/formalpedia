-- Prove2me | solution 1 for Couret.STROBO2TORS.pairRealization_injective_on
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:16.761188+00:00
-- url     : https://prove2.me/submissions/f699661a-e173-4b6d-9ac1-2fcce987b77c

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
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_parameters_unique
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_injective_on_two_torsion
import Definitions.Def_Couret_Strobo2TorsZeroFree_13701bff33aa
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators
namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G]







section Finite
variable [Fintype G]


























theorem mem_pairParameters (d v a u : G) :
    (⟨(d,v),(a,u)⟩ : PairParameter G) ∈ pairParameters ↔
      d+d=0 ∧ d ≠ 0 ∧ (v+v)+v=0 ∧ v ≠ 0 ∧ u+u=0 ∧
      0 ∉ paramSupport ((a,d),v) ∧
      0 ∉ translateSupport (paramSupport ((a,d),-v)) u := by
  simp only [pairParameters,Finset.mem_sigma,Finset.mem_product,Finset.mem_erase,
    mem_twoTorsion,mem_threeTorsion,pairLifts,Finset.mem_filter,Finset.mem_product,
    Finset.mem_univ,true_and]
  tauto



/-- Unique raw parameters ensure that this is a genuine count of ordered
pairs of supports, with no orientation or translation multiplicity. -/
theorem p2m_local_pairRealization_injective_on :
    Set.InjOn (pairRealization : PairParameter G → Finset G × Finset G) (pairParameters : Finset (PairParameter G)) := by
  rintro ⟨⟨d,v⟩,⟨a,u⟩⟩ hp ⟨⟨e,w⟩,⟨b,z⟩⟩ hq heq
  obtain ⟨hd,hd0,hv,hv0,hu,_,_⟩ := (mem_pairParameters d v a u).mp hp
  obtain ⟨he,he0,hw,hw0,hz,_,_⟩ := (mem_pairParameters e w b z).mp hq
  have hs := congrArg Prod.fst heq
  change paramSupport ((a,d),v) = paramSupport ((b,e),w) at hs
  obtain ⟨rfl,rfl,rfl⟩ := paramSupport_parameters_unique a d v b e w
    hd he hd0 he0 hv hw hv0 hw0 hs
  have ht := congrArg Prod.snd heq
  change translateSupport (paramSupport ((a,d),-v)) u =
    translateSupport (paramSupport ((a,d),-v)) z at ht
  have huz := translateSupport_injective_on_two_torsion (paramSupport ((a,d),-v))
    (paramSupport_card a d (-v) hd hd0 (three_torsion_neg v hv) (neg_ne_zero.mpr hv0))
    u z hu hz ht
  subst z
  rfl

attribute [local instance] Classical.propDecidable





























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Set.InjOn.{p2m_u_0, p2m_u_0} (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G)
    (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.pairRealization.{p2m_u_0} G inst inst_1)
    (@SetLike.coe.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G))
      (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G)
      (@Finset.instSetLike.{p2m_u_0} (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G))
      (@Couret.STROBO2TORS.pairParameters.{p2m_u_0} G inst inst_1 inst_2)) := @_root_.Couret.STROBO2TORS.p2m_local_pairRealization_injective_on

