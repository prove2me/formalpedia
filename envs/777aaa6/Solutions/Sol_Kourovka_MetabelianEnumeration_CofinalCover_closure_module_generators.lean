-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.CofinalCover.closure_module_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:15:10.664173+00:00
-- url     : https://prove2.me/submissions/db186d42-edc0-4983-9d70-220b10267e3f

import Definitions.Def_Kourovka_Cofinality_LatticePullback
import Definitions.Def_Kourovka_Modules_ModuleRealization
import Definitions.Def_Kourovka_Covers_CertifiedCover
import Definitions.Def_Kourovka_Modules_FiniteModuleGenerators
import Definitions.Def_Kourovka_Cofinality_CofinalRealization
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_projection_orderedWord
import Theorems.Thm_Kourovka_MetabelianEnumeration_CofinalCover_orderedWord_mem
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
import Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_smul_as_sum
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
theorem _root_.solution {a : ℕ} (t : Fin k → E)
    (ht : ∀ i, π (t i) = Multiplicative.ofAdd (Pi.single i 1))
    (hact : ActionCompatible (kernelInclusion π) t) (A : Fin a → Additive π.ker)
    (hA : Submodule.span (GroupRing (Lattice k)) (Set.range A) = ⊤) :
    Subgroup.closure (Set.range t ∪ Set.range (fun i => (A i).toMul.val)) = ⊤ := by
  let K := Subgroup.closure (Set.range t ∪ Set.range (fun i => (A i).toMul.val))
  have htK (i : Fin k) : t i ∈ K := Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  let B : AddSubgroup (Additive π.ker) := (K.comap π.ker.subtype).toAddSubgroup
  have hsmul (r : GroupRing (Lattice k)) (m : Additive π.ker) (hm : m ∈ B) :
      r • m ∈ B := by
    rw [smul_as_sum]
    apply B.list_sum_mem
    intro n hn
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hn
    apply B.zsmul_mem
    change (kernelInclusion π) (Multiplicative.ofAdd
      ((AddMonoidAlgebra.single u 1 : GroupRing (Lattice k)) • m)) ∈ K
    rw [hact]
    exact K.mul_mem (K.mul_mem (K.inv_mem (orderedWord_mem t K htK u)) hm)
      (orderedWord_mem t K htK u)
  let V : Submodule (GroupRing (Lattice k)) (Additive π.ker) := {
    carrier := B
    zero_mem' := B.zero_mem
    add_mem' := B.add_mem
    smul_mem' := hsmul }
  have hspan : Submodule.span (GroupRing (Lattice k)) (Set.range A) ≤ V := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : π.ker ≤ K := by
    intro n hn
    exact hspan (by rw [hA]; exact Submodule.mem_top (x := Additive.ofMul ⟨n, hn⟩))
  apply top_unique
  intro g _
  let w := orderedWord t (π g).toAdd
  have hw : w ∈ K := orderedWord_mem t K htK _
  have hn : g * w⁻¹ ∈ π.ker := by
    change π (g * w⁻¹) = 1
    rw [map_mul, map_inv, projection_orderedWord π t ht]
    simp
  have h := K.mul_mem (hker hn) hw
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
end Kourovka.MetabelianEnumeration.CofinalCover
