-- Prove2me | Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly
-- name    : mme_dwz_prescribed_z_finite_weighted_node_assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T16:55:26.869988+00:00
-- url     : https://prove2.me/theorems/87190585-945d-4e5f-a990-8926e5108005
-- title:
--   Finite tensor assembly datum at a partition node of a recursive prescribed-Z ledger
-- statement:
--   The tensor-side datum at one node of a recursive prescribed-Z construction whose children partition the parent's positions.
--
--   Child $i$ occupies $w_i$ of the synchronized child lengths and the parent occupies $w_P$ of them; for a partition $\sum_i w_i = w_P$, which the datum need not state because the restriction below already forces it. Given, at a common length $L_0 r$, a finite six-symmetrized witness for every child at its base $v_i$, the datum asserts a parent multiplicity with length $L_0 r w_P$, a family of $k \ge \rho^{L_0 r w_P}$ tensors restricting from the parent's prescribed Z power, an actual finite matrix extraction from the six-symmetrization of that family, and the weighted weight bound $k^6 (\prod_i v_i^{w_i})^{6 L_0 r} \le \sum_j (a_j b_j c_j)^\tau$.
--
--   It is the partition-node analogue of the equal-length node datum: children are synchronized once and then used at their own integer multiples of the common length, which is what a global node of a fourth-power construction requires, since there the components appear in proportion to their masses.
-- source:
--   Interface definition isolating the per-node tensor obligation for a partition node of the recursive restricted-value construction of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 7.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

/-- The tensor-side datum at one recursive node whose children **partition** the parent's
positions, each occupying its own integer multiple of the synchronized child length.

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
def PrescribedZFiniteWeightedNodeAssembly
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
    (weight : J → ℕ) (parentWeight : ℕ)
    (tau rho : ℝ) (v : J → ℝ) : Prop :=
  ∀ (L₀ r : ℕ) (mChild : J → ℕ),
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


