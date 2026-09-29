-- Prove2me | Theorems.Thm_mme_recursive_yz_boundary_profile_of_grade_support
-- name    : mme_recursive_yz_boundary_profile_of_grade_support
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T09:59:15.283854+00:00
-- url     : https://prove2.me/theorems/53d352ab-b0cd-4330-8263-dd4a8726056a
-- title:
--   Reconstructing a boundary profile from stage grade support
-- statement:
--   Let $A$ be a recursive Y/Z stage and $d$ one of its child cells, of multiplicity $L$. Write $g_i$ for its three coarse grades and $\mu_i(s)$ for its complete-word histograms. Suppose a mode $z$ has $g_z=0$ and every positive histogram entry has its prescribed grade:
--
--   $$\mu_i(s)>0\quad\Longrightarrow\quad\sum_r s_r=g_i.$$
--
--   Then there is an exact boundary profile $B$ of length $L$ whose three shapes and three histograms agree with those of $d$, in orientation $z$. Its free histogram is $\mu_1$ when $z=0$, $\mu_2$ when $z=1$, and $\mu_0$ when $z=2$. The zero-mode histogram is concentrated on the zero word, while the remaining histogram is obtained by the coordinatewise involution $s_r\mapsto 2-s_r$. The stage's stored mass and boundary identities suffice; no tensor map is assumed.
-- source:
--   Direct reconstruction from RecursiveYZ.Certificate.Stage mass, grade support, and boundary identities; matrix restriction by the exact boundary-profile extraction theorem.

import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary

theorem mme_recursive_yz_boundary_profile_of_grade_support
    {D : HashExtraction.HashData} (A : Stage D) (j : Fin A.childCells)
    (z : Fin 3) (hz : ((A.childCell j).2.val z).val = 0)
    (hg : ∀ i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ B : Boundary.Profile A.ell (A.childMultiplicity j),
      (∀ i, ((A.childCell j).2.val i).val = B.shape z i) ∧
      (∀ i, A.mu i (A.childCell j) = B.mu z i) := by sorry
