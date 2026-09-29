-- Prove2me | Definitions.Def_mme_more_asymmetry_template_mm_compatibility
-- name    : mme_more_asymmetry_template_mm_compatibility
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-12T17:18:17.891844+00:00
-- url     : https://prove2.me/theorems/3889766c-1f02-4d67-ab6a-b1357909c7e3
-- title:
--   More Asymmetry intact-template matrix compatibility
-- statement:
--   For a finite More Asymmetry bundle $D$ and concrete stages $A$, this interface records the finite profile information used by the intact-template algebra. Each factor's unbroken template restricts to a matrix-multiplication tensor with explicit local dimensions $(a_j,b_j,c_j)$, and the products of those local dimensions are exactly the declared target dimensions $(D.a,D.b,D.c)$. The record intentionally omits repaired copy counts, divisibility, budgets, and the final recursive assembly predicate; those are separate obligations.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 4.1, 5.1, and 6.1--6.6; finite constituent profile-to-matrix identifications and multiplicative matrix dimensions.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Definitions.Def_mme_CW_2376_address_block

open MME MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

namespace MME.RecursiveYZ.Certificate

/--
Finite source-level data for one intact-template matrix-multiplication copy.
The local dimensions describe the matrix tensor supplied by each factor's
intact template, while the product equalities identify the dimensions of the
assembled target. This record contains no copy-count, repair, or final
`RecursiveAssembly` assertion.
-/
structure MoreAsymmetryTemplateMMCompatibility
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (K : Type u) [Field K] where
  localA : Fin D.factors → ℕ
  localB : Fin D.factors → ℕ
  localC : Fin D.factors → ℕ
  factor_restrict :
    ∀ j, TensorObj.Restrict ((A j).template K)
      (MMObj K (localA j) (localB j) (localC j))
  product_a : (∏ j, localA j) = D.a
  product_b : (∏ j, localB j) = D.b
  product_c : (∏ j, localC j) = D.c

end MME.RecursiveYZ.Certificate


