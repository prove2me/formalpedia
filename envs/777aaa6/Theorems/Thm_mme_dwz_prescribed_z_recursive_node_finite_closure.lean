-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_recursive_node_finite_closure
-- name    : mme_dwz_prescribed_z_recursive_node_finite_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:48:56.079842+00:00
-- url     : https://prove2.me/theorems/a1cf8566-d5a1-4680-bca2-30f4b58314c5
-- title:
--   One recursive prescribed-Z node: children values plus a finite assembly give the parent value
-- statement:
--   Consider one node of a recursive prescribed-Z construction: a parent tensor with its Z-basis, grade and integer Z-split profile, and a finite family of children with theirs. Fix $\tau$, a retained rate $\rho \ge 0$, and for each child a base $v_i$ with $0 < v_i < V_i$, where $V_i$ is a value the child is already known to have:
--
--   $$V^{(6)}_{\tau}\big(\text{child}_i, \tilde\alpha_i\big) \;\ge\; V_i .$$
--
--   Suppose the node's **finite assembly** datum holds: at every common physical length $L_0 r$ at which all children have finite witnesses, there are a parent multiplicity $m$ with $\mathrm{length}(\tilde\alpha,m) = L_0 r$ and $r \le m$, a family of $k \ge \rho^{L_0 r}$ tensors restricting from the parent's prescribed power, a finite matrix extraction from the six-symmetrization of that family, and the weight bound
--
--   $$k^{6}\Big(\prod_i v_i\Big)^{6 L_0 r} \;\le\; \sum_j (a_j b_j c_j)^{\tau}.$$
--
--   Then the parent inherits the product value
--
--   $$V^{(6)}_{\tau}\big(\text{parent}, \tilde\alpha\big) \;\ge\; \rho \cdot \prod_i v_i .$$
--
--   Everything that is not tensor-specific is discharged here: the children are first synchronized to a common physical length, their witnesses are composed with the assembly's two restrictions, the sixth-power product arithmetic is carried out, cofinality in the parent multiplicity is established from $r \le m$, and the endpoint is lowered from the strict bases $v_i$ to the stated product by monotonicity.
--
--   This is the interface that lets a recursive value ledger be discharged node by node: each node supplies only its own finite tensor assembly, and every scalar and asymptotic step around it is already proved.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_dwz_prescribed_z_finite_node_assembly

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

theorem mme_dwz_prescribed_z_recursive_node_finite_closure
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
      (rho * ∏ i, v i) := by sorry
