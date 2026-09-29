-- Prove2me | Theorems.Thm_mme_more_asymmetry_template_mm_assembly
-- name    : mme_more_asymmetry_template_mm_assembly
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T17:24:15.853166+00:00
-- url     : https://prove2.me/theorems/ed4cc82f-4efa-41ee-a66d-4581e0578acf
-- title:
--   More Asymmetry one-copy template/MM assembly
-- statement:
--   Let $D$ be a finite More Asymmetry bundle and let $A$ attach concrete recursive stages. Assume the independently meaningful intact-template compatibility interface: each factor template restricts to a matrix-multiplication tensor with explicit local dimensions, and the products of those dimensions are $(D.a,D.b,D.c)$. Then the finite Kronecker product of the intact templates restricts to one $MMObj(K,D.a,D.b,D.c)$. This is the one-copy algebraic core of the template branch; it does not assert repaired multiplicities, divisibility, budgets, or the full `RecursiveAssembly` predicate.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Sections 4.1, 5.1, and 6.1--6.6. This finite one-copy adapter isolates the tensor-product MM dimension multiplication before repaired copy accounting.

import Definitions.Def_mme_more_asymmetry_template_mm_compatibility
import Theorems.Thm_mme_kronFin_MMObj_iso
import Definitions.Def_mme_tensor_quotient

open BigOperators MME MME.TensorObj MME.HashExtraction MME.RecursiveYZ.Certificate

set_option autoImplicit false

universe u

theorem mme_more_asymmetry_template_mm_assembly {K : Type u} [Field K]
    (D : HashExtraction.Data)
    (A : ∀ j, Stage (D.hash j))
    (hcompat : MoreAsymmetryTemplateMMCompatibility D A K) :
    TensorObj.Restrict
      (TensorObj.kronFin D.factors (fun j ↦ (A j).template K))
      (MMObj K D.a D.b D.c) := by sorry
