-- Prove2me | solution 1 for mme_dwz_prescribed_z_weighted_node_finite_closure_from
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T17:01:16.231988+00:00
-- url     : https://prove2.me/submissions/84216bdf-9632-4983-965e-72014fecf41e

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly_from
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_dwz_prescribed_z_six_finite_common_physical_length
import Theorems.Thm_mme_sixSymmetrization_restrict
import Mathlib.Tactic

/-!
# One recursive prescribed-Z node whose children partition the parent

The children are synchronized to a common length `L₀ * r` and then used at their own multiples
`L₀ * r * weight i`, so a node whose children partition the parent's positions — the global node of
a recursive value ledger — is covered, not only a node whose children each occupy the whole length.

The parent's value is whatever `V` satisfies `V ^ parentWeight ≤ rho ^ parentWeight * ∏ i, v i ^ weight i`,
which is the integer form of `V ≤ rho * ∏ i, v i ^ (weight i / parentWeight)`; the exponents
`weight i / parentWeight` are exactly the rational child coefficients a scalar ledger stores.
-/

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

private theorem weightedScalarPowerBound
    {J : Type w} [Fintype J]
    (rho V : ℝ) (v : J → ℝ) (weight : J → ℕ) (L pw k : ℕ)
    (hrho : 0 ≤ rho) (hV : 0 ≤ V) (hv : ∀ i, 0 < v i)
    (hVpow : V ^ pw ≤ rho ^ pw * ∏ i, v i ^ weight i)
    (hcard : rho ^ (L * pw) ≤ (k : ℝ)) :
    V ^ (6 * (L * pw)) ≤ (k : ℝ) ^ 6 * (∏ i, v i ^ weight i) ^ (6 * L) := by
  have hprod : 0 ≤ ∏ i, v i ^ weight i :=
    (Finset.prod_pos fun i _ ↦ pow_pos (hv i) _).le
  have hstep : V ^ (6 * (L * pw)) ≤ (rho ^ pw * ∏ i, v i ^ weight i) ^ (6 * L) := by
    have hpow : V ^ (6 * (L * pw)) = (V ^ pw) ^ (6 * L) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [hpow]
    exact pow_le_pow_left₀ (pow_nonneg hV pw) hVpow (6 * L)
  refine hstep.trans ?_
  have hsplit : (rho ^ pw * ∏ i, v i ^ weight i) ^ (6 * L)
      = (rho ^ (L * pw)) ^ 6 * (∏ i, v i ^ weight i) ^ (6 * L) := by
    rw [mul_pow]
    congr 1
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (pow_nonneg hrho _) hcard 6) (pow_nonneg hprod _)

private theorem sixFiniteWitness_mono_base
    {K : Type u} [Field K] {A : TensorObj K 3}
    {n : ℕ} {tau W V : ℝ}
    (hW : 0 ≤ W) (hWV : W ≤ V)
    (hV : SixFiniteWitness TensorObj.Restrict A n tau V) :
    SixFiniteWitness TensorObj.Restrict A n tau W := by
  rcases hV with ⟨q, a, b, c, hrestrict, hweight⟩
  refine ⟨q, a, b, c, hrestrict, ?_⟩
  exact (pow_le_pow_left₀ hW hWV (6 * n)).trans hweight

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
    (weight : J → ℕ) (parentWeight : ℕ) (threshold : ℕ)
    (tau rho : ℝ) (V v : J → ℝ) (W : ℝ)
    (hrho : 0 ≤ rho) (hW : 0 ≤ W) (hpw : 0 < parentWeight)
    (hWpow : W ^ parentWeight ≤ rho ^ parentWeight * ∏ i, v i ^ weight i)
    (hpos : ∀ i, 0 < v i) (hstrict : ∀ i, v i < V i)
    (hvalue : ∀ i, HasPrescribedZSixRestrictionValueAtLeast
      (child i) (childBasis i) (childGrade i) (childProfile i) tau (V i))
    (hassembly : PrescribedZFiniteWeightedNodeAssemblyFrom parent child
      parentBasis parentGrade parentProfile
      childBasis childGrade childProfile weight parentWeight threshold tau rho v) :
    HasPrescribedZSixRestrictionValueAtLeast
      parent parentBasis parentGrade parentProfile tau W := by
  classical
  obtain ⟨L₀, hL₀, hcommon⟩ :=
    mme_dwz_prescribed_z_six_finite_common_physical_length
      child childBasis childGrade childProfile
      tau V v hpos hstrict hvalue
  rw [HasPrescribedZSixRestrictionValueAtLeast, HasSixSequenceRate]
  refine ⟨hW, ?_⟩
  intro X hX hXtarget cutoff
  let r : ℕ := max (max cutoff 1) threshold
  let mChild : J → ℕ := fun i ↦ Classical.choose (hcommon r i)
  have hmChild : ∀ i, (childProfile i).length (mChild i) = L₀ * r :=
    fun i ↦ (Classical.choose_spec (hcommon r i)).1
  have hwChild : ∀ i, SixFiniteWitness TensorObj.Restrict
      (prescribedZPower (child i) (childBasis i) (childGrade i)
        (childProfile i) (mChild i))
      (L₀ * r) tau (v i) :=
    fun i ↦ (Classical.choose_spec (hcommon r i)).2
  obtain ⟨mParent, k, family, q, a, b, c,
      hrm, hlength, hcard, hinduced, hfamilyMM, hweight⟩ :=
    hassembly L₀ r mChild (le_max_right (max cutoff 1) threshold) hmChild hwChild
  have hcutR : cutoff ≤ r := le_trans (le_max_left cutoff 1) (le_max_left (max cutoff 1) threshold)
  have hcutM : cutoff ≤ mParent := hcutR.trans hrm
  have hrLength : r ≤ L₀ * r * parentWeight := by
    have h1 : r ≤ L₀ * r := by
      simpa [one_mul] using Nat.mul_le_mul_right r hL₀
    have h2 : L₀ * r ≤ L₀ * r * parentWeight := by
      simpa [mul_one] using Nat.mul_le_mul_left (L₀ * r) hpw
    exact h1.trans h2
  have hcutLength : cutoff ≤ parentProfile.length mParent := by
    rw [hlength]
    exact hcutR.trans hrLength
  refine ⟨mParent, hcutM, hcutLength, ?_⟩
  rw [hlength]
  refine sixFiniteWitness_mono_base hX.le hXtarget.le ?_
  refine ⟨q, a, b, c, TensorObj.Restrict.trans hfamilyMM
    (mme_sixSymmetrization_restrict hinduced), ?_⟩
  exact (weightedScalarPowerBound rho W v weight (L₀ * r) parentWeight k
    hrho hW hpos hWpow hcard).trans hweight
