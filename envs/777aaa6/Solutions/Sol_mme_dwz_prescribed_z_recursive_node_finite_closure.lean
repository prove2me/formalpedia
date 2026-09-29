-- Prove2me | solution 1 for mme_dwz_prescribed_z_recursive_node_finite_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:48:58.281242+00:00
-- url     : https://prove2.me/submissions/f3d54cc8-bb02-41db-9cab-a0496c1c2628

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_finite_node_assembly
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_dwz_prescribed_z_six_finite_common_physical_length
import Theorems.Thm_mme_sixSymmetrization_restrict
import Mathlib.Tactic

/-!
# One-node recursive prescribed-Z closure

This theorem separates the already-public common-length synchronization from
the one genuinely tensor-specific finite assembly premise.  The latter exposes
the induced-family restriction, its six-symmetric MM extraction, and the two
finite scalar bounds.  Everything after those data--restriction composition,
the sixth-power product calculation, cofinality, and endpoint monotonicity--is
proved here.
-/

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

private theorem nodeScalarPowerBound
    {J : Type w} [Fintype J]
    (rho : ℝ) (v : J → ℝ) (L k : ℕ)
    (hrho : 0 ≤ rho) (hv : ∀ i, 0 < v i)
    (hcard : rho ^ L ≤ (k : ℝ)) :
    (rho * ∏ i, v i) ^ (6 * L) ≤
      (k : ℝ) ^ 6 * (∏ i, v i) ^ (6 * L) := by
  have hprod : 0 ≤ ∏ i, v i :=
    (Finset.prod_pos fun i _ ↦ hv i).le
  have hcardSix : (rho ^ L) ^ 6 ≤ (k : ℝ) ^ 6 :=
    pow_le_pow_left₀ (pow_nonneg hrho L) hcard 6
  calc
    (rho * ∏ i, v i) ^ (6 * L) =
        (rho ^ L) ^ 6 * (∏ i, v i) ^ (6 * L) := by
      rw [mul_pow]
      congr 1
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ (k : ℝ) ^ 6 * (∏ i, v i) ^ (6 * L) :=
      mul_le_mul_of_nonneg_right hcardSix (pow_nonneg hprod _)

private theorem sixFiniteWitness_mono_base
    {K : Type u} [Field K] {A : TensorObj K 3}
    {n : ℕ} {tau W V : ℝ}
    (hW : 0 ≤ W) (hWV : W ≤ V)
    (hV : SixFiniteWitness TensorObj.Restrict A n tau V) :
    SixFiniteWitness TensorObj.Restrict A n tau W := by
  rcases hV with ⟨q, a, b, c, hrestrict, hweight⟩
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  exact (pow_le_pow_left₀ hW hWV (6 * n)).trans hweight

private theorem common_parent_finite_witnesses
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (parent : TensorObj K 3) (child : J → TensorObj K 3)
    {ιParent : Type u} {tParent : ℕ}
    (parentBasis : Basis ιParent K (parent.V 2))
    (parentGrade : ιParent → Fin tParent)
    (parentProfile : IntegerZSplitProfile tParent)
    {ι : J → Type u} {t : J → ℕ}
    (childBasis : (i : J) → Basis (ι i) K ((child i).V 2))
    (childGrade : (i : J) → ι i → Fin (t i))
    (childProfile : (i : J) → IntegerZSplitProfile (t i))
    (tau rho : ℝ) (V v : J → ℝ)
    (hrho : 0 ≤ rho)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (child i) (childBasis i) (childGrade i) (childProfile i) tau (V i))
    (hassembly : PrescribedZFiniteNodeAssembly parent child
      parentBasis parentGrade parentProfile
      childBasis childGrade childProfile tau rho v) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ r : ℕ, ∃ mParent : ℕ,
      r ≤ mParent ∧ parentProfile.length mParent = L₀ * r ∧
      SixFiniteWitness TensorObj.Restrict
        (prescribedZPower parent parentBasis parentGrade parentProfile mParent)
        (L₀ * r) tau (rho * ∏ i, v i) := by
  classical
  obtain ⟨L₀, hL₀, hcommon⟩ :=
    mme_dwz_prescribed_z_six_finite_common_physical_length
      child childBasis childGrade childProfile
      tau V v hpos hstrict hvalue
  refine ⟨L₀, hL₀, ?_⟩
  intro r
  let mChild : J → ℕ := fun i ↦ Classical.choose (hcommon r i)
  have hmChild : ∀ i,
      (childProfile i).length (mChild i) = L₀ * r := by
    intro i
    exact (Classical.choose_spec (hcommon r i)).1
  have hwChild : ∀ i, SixFiniteWitness TensorObj.Restrict
      (prescribedZPower (child i) (childBasis i) (childGrade i)
        (childProfile i) (mChild i))
      (L₀ * r) tau (v i) := by
    intro i
    exact (Classical.choose_spec (hcommon r i)).2
  obtain ⟨mParent, k, family, q, a, b, c,
      hrm, hlength, hcard, hinduced, hfamilyMM, hweight⟩ :=
    hassembly L₀ r mChild hmChild hwChild
  refine ⟨mParent, hrm, hlength, q, a, b, c, ?_, ?_⟩
  · exact TensorObj.Restrict.trans hfamilyMM
      (mme_sixSymmetrization_restrict hinduced)
  · exact (nodeScalarPowerBound rho v (L₀ * r) k
      hrho hpos hcard).trans hweight

/-- Synchronized finite child witnesses and one induced-family assembly close
the parent recursive node.  No synchronization, root extraction, or scalar
product premise remains in the conclusion. -/
theorem solution
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (parent : TensorObj K 3) (child : J → TensorObj K 3)
    {ιParent : Type u} {tParent : ℕ}
    (parentBasis : Basis ιParent K (parent.V 2))
    (parentGrade : ιParent → Fin tParent)
    (parentProfile : IntegerZSplitProfile tParent)
    {ι : J → Type u} {t : J → ℕ}
    (childBasis : (i : J) → Basis (ι i) K ((child i).V 2))
    (childGrade : (i : J) → ι i → Fin (t i))
    (childProfile : (i : J) → IntegerZSplitProfile (t i))
    (tau rho : ℝ) (V v : J → ℝ)
    (hrho : 0 ≤ rho)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (child i) (childBasis i) (childGrade i) (childProfile i) tau (V i))
    (hassembly : PrescribedZFiniteNodeAssembly parent child
      parentBasis parentGrade parentProfile
      childBasis childGrade childProfile tau rho v) :
    HasPrescribedZSixRestrictionValueAtLeast
      parent parentBasis parentGrade parentProfile tau
      (rho * ∏ i, v i) := by
  classical
  obtain ⟨L₀, hL₀, hparent⟩ := common_parent_finite_witnesses
    parent child parentBasis parentGrade parentProfile
    childBasis childGrade childProfile tau rho V v hrho
    hpos hstrict hvalue hassembly
  rw [HasPrescribedZSixRestrictionValueAtLeast, HasSixSequenceRate]
  have hproduct : 0 ≤ ∏ i, v i :=
    (Finset.prod_pos fun i _ ↦ hpos i).le
  refine ⟨mul_nonneg hrho hproduct, ?_⟩
  intro W hW hWtarget cutoff
  let r : ℕ := max cutoff 1
  obtain ⟨mParent, hrm, hlength, hwitness⟩ := hparent r
  have hcutR : cutoff ≤ r := le_max_left cutoff 1
  have hcutM : cutoff ≤ mParent := hcutR.trans hrm
  have hLone : 1 ≤ L₀ := hL₀
  have hrLength : r ≤ L₀ * r := by
    simpa [one_mul] using Nat.mul_le_mul_right r hLone
  have hcutLength : cutoff ≤ parentProfile.length mParent := by
    rw [hlength]
    exact hcutR.trans hrLength
  refine ⟨mParent, hcutM, hcutLength, ?_⟩
  rw [hlength]
  exact sixFiniteWitness_mono_base hW.le hWtarget.le hwitness
