-- Prove2me | Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly_from_length
-- name    : mme_dwz_prescribed_z_finite_weighted_node_assembly_from_length
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T17:44:19.524127+00:00
-- url     : https://prove2.me/theorems/1a41f435-1cd8-4d6e-b504-ac66ef538bcd
-- title:
--   Partition-node tensor assembly datum, beyond a threshold length
-- statement:
--   The tensor-side datum at a partition node of a recursive prescribed-Z construction, required only beyond a threshold **physical length**.
--
--   Child $i$ occupies $w_i$ of the synchronized child lengths and the parent $w_P$ of them. Given, at a common length $L_0 r$ at least the threshold, a finite six-symmetrized witness for every child at its base $v_i$, the datum asserts a parent multiplicity of length $L_0 r w_P$, a family of $k \ge \rho^{L_0 r w_P}$ tensors restricting from the parent's prescribed Z power, an actual finite matrix extraction from the six-symmetrization of that family, and the weighted bound $k^6 (\prod_i v_i^{w_i})^{6 L_0 r} \le \sum_j (a_j b_j c_j)^\tau$.
--
--   Putting the threshold on the length $L_0 r$ rather than on $r$ alone matters twice: it makes the datum available to an extraction that holds only eventually in its scaling parameter, and it excludes the degenerate $L_0 = 0$, where the parent length would collapse to zero while the conclusion still demands a multiplicity at least $r$.
-- source:
--   Interface definition isolating the per-node tensor obligation for a partition node of the recursive restricted-value construction of Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 7, in the form available from an eventually-valid extraction.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

/-- The tensor-side datum at one recursive node whose children **partition** the parent's
positions, each occupying its own integer multiple of the synchronized child length, and whose
construction becomes available only beyond a threshold physical length.

`weight i` is the number of common child lengths that child `i` occupies and `parentWeight` the
number the parent occupies; for a partition node `∑ i, weight i = parentWeight`, which the datum
does not have to state because the restriction below already forces it.

Stated at the common physical length supplied by
`mme_dwz_prescribed_z_six_finite_common_physical_length`: each child is given a witness at
`L₀ * r`, and is used at `L₀ * r * weight i`, which the accepted prescribed-Z witness-power
theorem supplies.

The first restriction is the induced family extraction into the parent's prescribed Z power, the
second is the finite matrix extraction after six-symmetrizing that family, and the two inequalities
record the retained family rate and the weighted product of the synchronized child weights. -/
def PrescribedZFiniteWeightedNodeAssemblyFromLength
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
    (tau rho : ℝ) (v : J → ℝ) : Prop :=
  ∀ (L₀ r : ℕ) (mChild : J → ℕ),
    threshold ≤ L₀ * r →
    (∀ i, (childProfile i).length (mChild i) = L₀ * r) →
    (∀ i, SixFiniteWitness TensorObj.Restrict
      (prescribedZPower (child i) (childBasis i) (childGrade i)
        (childProfile i) (mChild i))
      (L₀ * r) tau (v i)) →
    ∃ (mParent k : ℕ) (family : Fin k → TensorObj K 3)
        (q : ℕ) (a b c : Fin q → ℕ),
      r ≤ mParent ∧
      parentProfile.length mParent = L₀ * r * parentWeight ∧
      rho ^ (L₀ * r * parentWeight) ≤ (k : ℝ) ∧
      TensorObj.Restrict (TensorObj.bigAdd family)
        (prescribedZPower parent parentBasis parentGrade parentProfile mParent) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.bigAdd family)) ∧
      (k : ℝ) ^ 6 * (∏ i, v i ^ weight i) ^ (6 * (L₀ * r)) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)


