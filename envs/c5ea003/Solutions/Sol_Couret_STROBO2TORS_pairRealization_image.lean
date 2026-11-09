-- Prove2me | solution 1 for Couret.STROBO2TORS.pairRealization_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:39:14.364033+00:00
-- url     : https://prove2.me/submissions/07cd1e9b-54ca-4565-9cbf-eec81b057117

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
import Theorems.Thm_Couret_STROBO2TORS_mem_orderedNontranslationPairs
import Theorems.Thm_Couret_STROBO2TORS_mem_threeTorsion
import Theorems.Thm_Couret_STROBO2TORS_nontranslationCollision_param_iff
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





attribute [local instance] Classical.propDecidable





theorem p2m_local_pairRealization_image :
    (pairParameters : Finset (PairParameter G)).image pairRealization = orderedNontranslationPairs := by
  ext p
  rcases p with ⟨S,T⟩
  rw [mem_orderedNontranslationPairs,nontranslationCollision_param_iff]
  constructor
  · rintro h
    obtain ⟨⟨⟨d,v⟩,⟨a,u⟩⟩,hp,heq⟩ := Finset.mem_image.mp h
    obtain ⟨hd,hd0,hv,hv0,hu,hS,hT⟩ := (mem_pairParameters d v a u).mp hp
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj heq
    exact ⟨a,d,v,u,hd,hd0,hv,hv0,hu,rfl,rfl,hS,hT⟩
  · rintro ⟨a,d,v,u,hd,hd0,hv,hv0,hu,rfl,rfl,hS,hT⟩
    exact Finset.mem_image.mpr ⟨⟨(d,v),(a,u)⟩,
      (mem_pairParameters d v a u).mpr ⟨hd,hd0,hv,hv0,hu,hS,hT⟩,rfl⟩























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G],
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)))
    (@Finset.image.{p2m_u_0, p2m_u_0} (Couret.STROBO2TORS.PairParameter.{p2m_u_0} G)
      (Prod.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G))
      (fun a b =>
        @instDecidableEqProd.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} G)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
          (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b) a b)
      (@Couret.STROBO2TORS.pairRealization.{p2m_u_0} G inst inst_1)
      (@Couret.STROBO2TORS.pairParameters.{p2m_u_0} G inst inst_1 inst_2))
    (@Couret.STROBO2TORS.orderedNontranslationPairs.{p2m_u_0} G inst inst_1 inst_2) := @_root_.Couret.STROBO2TORS.p2m_local_pairRealization_image

