-- Prove2me | Definitions.Def_mme_dwz_prescribed_z_finite_node_assembly
-- name    : mme_dwz_prescribed_z_finite_node_assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-20T14:47:27.014307+00:00
-- url     : https://prove2.me/theorems/03319824-3936-457e-a05d-b286eb0a6a45
-- title:
--   Finite tensor assembly datum at one recursive prescribed-Z node
-- statement:
--   The tensor-side datum required at one node of a recursive prescribed-Z value construction.
--
--   Fix a parent tensor with its Z basis, grade and integer Z-split profile, and a finite family of children with theirs; fix a symmetrization exponent $\tau$, a retained rate $\rho$ and per-child bases $v_i$. The datum says: for every common physical length $L_0 r$ at which all children carry finite six-symmetrized witnesses at their bases, there exist a parent multiplicity $m$ with $r \le m$ and $\mathrm{length}(\tilde\alpha, m) = L_0 r$, a finite family of $k \ge \rho^{L_0 r}$ tensors restricting from the parent's prescribed Z power, and an actual finite direct sum of matrix-multiplication tensors restricting from the six-symmetrization of that family, whose total $\tau$-weight is at least $k^6 (\prod_i v_i)^{6 L_0 r}$.
--
--   It isolates exactly the part of a recursive node that is specific to the tensors involved: the induced mode-disjoint family extraction, its six-symmetric matrix extraction, and the two finite scalar bounds. Synchronization of the children, the product arithmetic, cofinality and endpoint monotonicity are not part of this datum; they are proved once, generically, by the companion closure theorem.
-- source:
--   Interface definition isolating the per-node tensor obligation of the recursive restricted-value construction of Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 3.9 and Section 7.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

/-- The exact tensor-side data required at one recursive node.  It is stated at
the common physical length supplied by
`mme_dwz_prescribed_z_six_finite_common_physical_length`.

The first restriction is the induced mode-disjoint family extraction.  The
second is the finite MM extraction after six-symmetrizing that family.  The two
inequalities respectively record the retained family rate and the lossless
product of the synchronized child weights. -/
def PrescribedZFiniteNodeAssembly
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
      parentProfile.length mParent = L₀ * r ∧
      rho ^ (L₀ * r) ≤ (k : ℝ) ∧
      TensorObj.Restrict (TensorObj.bigAdd family)
        (prescribedZPower parent parentBasis parentGrade parentProfile mParent) ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.bigAdd family)) ∧
      (k : ℝ) ^ 6 * (∏ i, v i) ^ (6 * (L₀ * r)) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)


