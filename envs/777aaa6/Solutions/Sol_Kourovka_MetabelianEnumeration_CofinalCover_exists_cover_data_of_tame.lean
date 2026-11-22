-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.exists_cover_data_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:17:15.161706+00:00
-- url     : https://prove2.me/submissions/69eb995b-d8ca-4311-b4c0-e358b5b22c86

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_rightComm_eq_one_of_commute
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_closure_module_generators
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_finite_generators_with_designated
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_abs_unitSign
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_blockWord_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_conjugate_one
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_add
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_neg
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_euclidean_norm_abs
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_lower_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_neg_mem_ball
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_not_precedes_self
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_orderedWord_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_lower
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_shift
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_castSucc
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_raise_snoc_last
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_finRange
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shiftList_nil
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_Collection_shift_zero
import Theorems.Thm_Kourovka_MetabelianEnumeration_FiniteCover_realizationHom_surjective
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_finite_realizing_polynomials
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.abs_unitSign
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.blockWord_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.conjugate_one
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_add
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_neg
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.euclidean_norm_abs
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.lower_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.neg_mem_ball
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.not_precedes_self
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.orderedWord_zero
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_lower
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_shift
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_castSucc
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.raise_snoc_last
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_finRange
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shiftList_nil
attribute [local simp] Kourovka.MetabelianEnumeration.FiniteCover.Collection.shift_zero



set_option autoImplicit true
noncomputable section
set_option maxHeartbeats 50000
set_option autoImplicit false
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.CofinalCover
open FiniteCover CommutatorModule ModuleRealization ValuationModule SignedTameness
open TamenessCompactness
variable {k : ℕ} {E : Type} [Group E]
variable (π : E →* Multiplicative (Lattice k))
variable [IsMulCommutative π.ker]
variable [Module (GroupRing (Lattice k)) (Additive π.ker)]
namespace Kourovka.MetabelianEnumeration.CofinalCover
theorem _root_.solution (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t)
    [Module.Finite (GroupRing (Lattice k)) (Additive π.ker)]
    (htame : Tame (k := k) (Additive π.ker)) :
    ∃ a : ℕ, 1 ≤ a ∧ ∃ data : Datum k a,
      ConeVerifier.ConeCover (data.polynomials.map polynomialSupport) ∧
      ∀ radius : ℕ, ∃ f : FiniteCover.GroupOf data radius →* E, Function.Surjective f := by
  classical
  let c : Fin k × Fin k → Additive π.ker := fun ij => Additive.ofMul
    ⟨rightComm (t ij.1) (t ij.2), by
      change π (rightComm (t ij.1) (t ij.2)) = 1
      simp [rightComm, mul_comm, mul_assoc]⟩
  obtain ⟨a, ha, A, designated, hspan, hAd⟩ := finite_generators_with_designated c
  obtain ⟨ps, hps, hcone⟩ := finite_realizing_polynomials (kernelInclusion π) t hact htame
  let data : Datum k a := ⟨designated, ps⟩
  refine ⟨a, ha, data, hcone, ?_⟩
  intro radius
  have hr : Realizes data radius t (fun i => (A i).toMul.val) := {
    t_comm := by
      intro i j _
      rw [show data.designated i j = designated i j from rfl, hAd]
      rfl
    short_comm := by
      intro i j v _
      let n : π.ker := ⟨conjugate (A j).toMul.val (orderedWord t v), by
        change π (conjugate (A j).toMul.val (orderedWord t v)) = 1
        have hj : π (A j).toMul.val = 1 := (A j).toMul.property
        simp [conjugate, hj]⟩
      have h : rightComm (A i).toMul n = 1 :=
        rightComm_eq_one_of_commute _ _ (mul_comm _ _)
      exact congrArg Subtype.val h
    polynomial := by
      intro i p hp
      exact hps p hp (A i) }
  exact ⟨realizationHom data radius t (fun i => (A i).toMul.val) hr,
    realizationHom_surjective data radius t (fun i => (A i).toMul.val) hr
      (closure_module_generators π t ht hact A hspan)⟩
end Kourovka.MetabelianEnumeration.CofinalCover
