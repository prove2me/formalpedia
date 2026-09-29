-- Prove2me | Theorems.Thm_mme_recursive_yz_boundary_matrix_extraction_of_grade_support
-- name    : mme_recursive_yz_boundary_matrix_extraction_of_grade_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T09:59:22.561641+00:00
-- url     : https://prove2.me/theorems/77489ff1-33fb-4497-acf4-c7a603761b4b
-- title:
--   Automatic matrix extraction for grade-supported boundary children
-- statement:
--   Let $A$ be a recursive Y/Z stage, $d$ a child cell of multiplicity $L$, and $K$ any field. Suppose its coarse grade is zero in a mode $z$, and each positive entry of each mode histogram has the prescribed coarse grade. Then there is a boundary profile $B$ matching the child, together with an actual restriction
--
--   $$\langle a_z,b_z,c_z\rangle_K\ \preceq\ T_d.$$
--
--   Here $T_d$ is the intact child tensor. If $\nu$ is the free histogram of $B$, its matrix dimension is
--
--   $$M=\frac{L!}{\prod_s \nu(s)!}\,5^{\sum_s\nu(s)\,\#\{r:s_r=1\}},$$
--
--   and $(a_z,b_z,c_z)$ is $(1,1,M)$, $(M,1,1)$, or $(1,M,1)$ according as $z=0,1,2$. The theorem supplies both the boundary-child certificate and the matrix restriction from scalar grade support and the stage's existing fields, without requiring an input extraction map.
-- source:
--   Direct reconstruction from RecursiveYZ.Certificate.Stage mass, grade support, and boundary identities; matrix restriction by the exact boundary-profile extraction theorem.

import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary

theorem mme_recursive_yz_boundary_matrix_extraction_of_grade_support
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (j : Fin A.childCells)
    (z : Fin 3) (hz : ((A.childCell j).2.val z).val = 0)
    (hg : ∀ i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ B : Boundary.Profile A.ell (A.childMultiplicity j),
      A.BoundaryChild j (B.a z) (B.b z) (B.c z) ∧
      Restrict (MMObj K (B.a z) (B.b z) (B.c z)) (A.childTensor K j) := by sorry
