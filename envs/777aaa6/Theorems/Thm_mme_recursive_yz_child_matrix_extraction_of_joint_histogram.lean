-- Prove2me | Theorems.Thm_mme_recursive_yz_child_matrix_extraction_of_joint_histogram
-- name    : mme_recursive_yz_child_matrix_extraction_of_joint_histogram
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:22:28.677082+00:00
-- url     : https://prove2.me/theorems/92bad623-de86-41fe-b810-409d98e89d75
-- title:
--   Child matrix extraction from integer joint profiles
-- statement:
--   Let $A$ be a recursive stage and $j$ one of its child cells. Suppose every positive entry in each prescribed complete-word histogram $\mu_i$ has the cell's prescribed mode grade. Let $\lambda(v_0,v_1,v_2)$ be nonnegative integer counts whose three marginals are $\mu_i$, and whose positive entries satisfy
--   $$v_0(r)+v_1(r)+v_2(r)=2$$
--   at every elementary position $r$. Define
--   $$n_{ik}=\sum_v\lambda(v)\,|\{r:v_i(r)=v_k(r)=1\}|.$$
--   Then the intact child tensor admits
--   $$\langle5^{n_{02}},5^{n_{01}},5^{n_{12}}\rangle_K\preceq T_j$$
--   over any field $K$. The joint mass need not be supplied separately: the stage's mass identities and the marginal equations determine it. The conclusion applies to boundary and interior cells at every recursive level.
-- source:
--   Stage mass identities, exact boundary-profile reconstruction, and intact-block matrix extraction from joint histograms.

import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
import Theorems.Thm_mme_recursive_yz_boundary_profile_of_grade_support

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

theorem mme_recursive_yz_child_matrix_extraction_of_joint_histogram
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (j : Fin A.childCells)
    (joint : (Fin 3 → CompleteWord A.ell) → ℕ)
    (hmarginal : ∀ i s, ∑ v, (if v i = s then joint v else 0) =
      A.mu i (A.childCell j) s)
    (hgrade : ∀ i s, 0 < A.mu i (A.childCell j) s →
      grade s = ((A.childCell j).2.val i).val)
    (hsupport : ∀ v, 0 < joint v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun i k ↦ ∑ v, joint v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
    Restrict (MMObj K (5 ^ n 0 2) (5 ^ n 0 1) (5 ^ n 1 2))
      (A.childTensor K j) := by sorry
