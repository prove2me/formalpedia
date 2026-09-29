-- Prove2me | Theorems.Thm_mme_recursive_yz_child_plan_of_interior_joint_histograms
-- name    : mme_recursive_yz_child_plan_of_interior_joint_histograms
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:22:08.428191+00:00
-- url     : https://prove2.me/theorems/7893d06f-f42f-43b6-abb4-59c7b4703330
-- title:
--   Recursive child plans from exact boundary profiles and interior joint counts
-- statement:
--   Let $A$ be a recursive stage whose prescribed complete-word histograms are supported on the prescribed grades. For each interior child cell $j$—one with all three grades positive—suppose nonnegative integer joint counts $\lambda_j(v_0,v_1,v_2)$ have the prescribed marginals and are supported on triples satisfying $v_0(r)+v_1(r)+v_2(r)=2$ at every elementary position.
--
--   There is a child plan for the entire stage over any field $K$. Boundary cells have exact boundary-profile certificates, while every interior cell has an actual matrix extraction with dimensions
--   $$a_j=5^{n_{j,02}},\qquad b_j=5^{n_{j,01}},\qquad c_j=5^{n_{j,12}},$$
--   where
--   $$n_{j,ik}=\sum_v\lambda_j(v)\,|\{r:v_i(r)=v_k(r)=1\}|.$$
--   No joint-count constraints are required on boundary cells. Their exact profiles retain the boundary multiplicities. The interior dimensions come from a fixed supported assignment; the statement does not assert further interior multiplicity gains or a global asymptotic rate.
-- source:
--   Stage mass identities, exact boundary-profile reconstruction, and intact-block matrix extraction from joint histograms.

import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
import Theorems.Thm_mme_recursive_yz_boundary_profile_of_grade_support

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

theorem mme_recursive_yz_child_plan_of_interior_joint_histograms
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D)
    (joint : Fin A.childCells → (Fin 3 → CompleteWord A.ell) → ℕ)
    (hgrade : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      grade s = ((A.childCell j).2.val i).val)
    (hmarginal : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ i s, ∑ v, (if v i = s then joint j v else 0) = A.mu i (A.childCell j) s)
    (hsupport : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ v, 0 < joint j v → ∀ r,
        (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun j i k ↦ ∑ v, joint j v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
    ∃ M : A.ChildPlan K, ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      M.a j = 5 ^ n j 0 2 ∧ M.b j = 5 ^ n j 0 1 ∧ M.c j = 5 ^ n j 1 2 := by sorry
