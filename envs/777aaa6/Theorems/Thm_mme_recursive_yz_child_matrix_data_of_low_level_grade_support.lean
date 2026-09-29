-- Prove2me | Theorems.Thm_mme_recursive_yz_child_matrix_data_of_low_level_grade_support
-- name    : mme_recursive_yz_child_matrix_data_of_low_level_grade_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:01:17.738562+00:00
-- url     : https://prove2.me/theorems/8a2b236b-065d-4399-ab50-08b4248b8352
-- title:
--   Complete child matrix data from grade support at the lowest recursive levels
-- statement:
--   Let $A$ be a recursive Y/Z stage with level $\ell\leq 1$, over any field $K$. Suppose every child-cell histogram is supported on the prescribed grade:
--
--   $$\mu_i(d,s)>0\quad\Longrightarrow\quad\sum_r s_r=g_i(d)$$
--
--   for every child cell $d$, mode $i$, and complete word $s$. Then there exists a full family of child matrix dimensions $a_d,b_d,c_d$ and actual restrictions
--
--   $$\langle a_d,b_d,c_d\rangle_K\ \preceq\ T_d$$
--
--   such that every member has an exact boundary-child certificate. Thus the entire child matrix-data structure is supplied by the scalar grade conditions and the stage's existing mass and boundary identities at these levels. The dimensions are those of matching boundary profiles; no interior extraction hypothesis is needed. This supplies local child data, without asserting the global repair budgets or asymptotic rate estimate.
-- source:
--   Boundary profile reconstruction and exact boundary extraction; at level at most one, the child grades sum to two and at least one is zero.

import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary

theorem mme_recursive_yz_child_matrix_data_of_low_level_grade_support
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (hlevel : A.ell ≤ 1)
    (hg : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ M : A.ChildMM K, ∀ j, A.BoundaryChild j (M.a j) (M.b j) (M.c j) := by sorry
