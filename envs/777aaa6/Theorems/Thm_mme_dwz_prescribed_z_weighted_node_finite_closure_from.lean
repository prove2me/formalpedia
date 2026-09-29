-- Prove2me | Theorems.Thm_mme_dwz_prescribed_z_weighted_node_finite_closure_from
-- name    : mme_dwz_prescribed_z_weighted_node_finite_closure_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T17:01:04.361298+00:00
-- url     : https://prove2.me/theorems/40b1450b-6fe2-464f-97e2-e02776e7c2cb
-- title:
--   A partition node closes from its children, with the assembly required only beyond a threshold
-- statement:
--   Consider one node of a recursive prescribed-Z construction whose children **partition** the parent's positions: child $i$ occupies $w_i$ of the common child lengths and the parent occupies $w_P$ of them, so that for a partition $\sum_i w_i = w_P$.
--
--   The construction is required only beyond a threshold multiplicity, which is what an extraction that holds eventually in its scaling parameter can supply.
--
--   Suppose each child already has a value $V_i$, fix bases $v_i$ with $0 < v_i < V_i$, and suppose the node's weighted finite assembly datum holds — at every common length $L_0 r$ at which all children have witnesses, it produces a parent multiplicity with $\mathrm{length} = L_0 r w_P$, a family of $k \ge \rho^{L_0 r w_P}$ tensors restricting from the parent's prescribed power, a matrix extraction from the six-symmetrization of that family, and the weight bound
--
--   $$k^6 \Big(\prod_i v_i^{\,w_i}\Big)^{6 L_0 r} \;\le\; \sum_j (a_j b_j c_j)^{\tau}.$$
--
--   Then for any $W \ge 0$ with
--
--   $$W^{\,w_P} \;\le\; \rho^{\,w_P} \prod_i v_i^{\,w_i},$$
--
--   the parent has value at least $W$. The displayed condition is the integer form of $W \le \rho \prod_i v_i^{\,w_i / w_P}$, and the exponents $w_i / w_P$ are precisely the rational child coefficients that a scalar value ledger stores for that node.
--
--   This is the partition-node companion of the equal-length node closure. The equal-length form applies when every child occupies the whole parent length; a node whose children divide the parent's positions among themselves — the global node of a fourth-power construction, where the components appear in proportion to their masses — needs this weighted form. Children are synchronized once at a common length and then used at their own multiples of it.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_dwz_prescribed_z_finite_weighted_node_assembly_from
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME BigOperators
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u w

set_option autoImplicit false

theorem mme_dwz_prescribed_z_weighted_node_finite_closure_from
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
      parent parentBasis parentGrade parentProfile tau W := by sorry
