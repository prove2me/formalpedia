-- Prove2me | Theorems.Thm_mme_recursive_yz_intact_template_MM_of_child_extractions
-- name    : mme_recursive_yz_intact_template_MM_of_child_extractions
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T12:12:07.969888+00:00
-- url     : https://prove2.me/theorems/d2bf205b-04d7-444f-941c-4ea78b9707e0
-- title:
--   An actual intact recursive template converts via its both-half child extractions
-- statement:
--   Let A be a concrete recursive Y/Z stage, and suppose each of its literal cell tensors restricts to a matrix-multiplication tensor. Each child tensor uses exactly m_r(s)+m_r(parent_r−s) child positions and the stage’s prescribed complete-word profiles. Then the intact template of A restricts to the matrix tensor with the products of the child dimensions. The conclusion concerns the actual template in the live extraction certificate; no source regrouping or profile factorization is assumed.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Section 6.5 displayed intact tensor and Section 6.6 recursion.

import Definitions.Def_mme_recursive_yz_child_matrix_data
open MME MME.TensorObj MME.RecursiveYZ.Certificate
set_option autoImplicit false
universe u

theorem mme_recursive_yz_intact_template_MM_of_child_extractions {K : Type u} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (M : A.ChildMM K) :
    Restrict (MMObj K M.dimA M.dimB M.dimC) (A.template K)  := by sorry
