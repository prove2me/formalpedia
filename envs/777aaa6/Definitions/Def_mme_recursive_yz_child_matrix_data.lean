-- Prove2me | Definitions.Def_mme_recursive_yz_child_matrix_data
-- name    : mme_recursive_yz_child_matrix_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T12:08:03.701154+00:00
-- url     : https://prove2.me/theorems/bf91ac4c-c0c8-4daa-9e0c-3c3a9c706086
-- title:
--   Literal recursive child tensors with both-half multiplicities and matrix extractions
-- statement:
--   For each concrete recursive Y/Z stage, enumerate its actual physical cells. The child power assigned to cell (r,s) is exactly m_r(s)+m_r(parent_r−s). Its tensor is the literal CW5 power with that multiplicity and the specified exact grade and complete-word histogram in all three modes. A child matrix certificate supplies three matrix dimensions and a restriction from that matrix tensor to each actual child tensor. The aggregate dimensions are their products. This data makes no assumption about conversion of the enclosing intact template; that is proved separately.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Section 6.5 displayed intact child tensor and Section 6.6 recursive assembly.

import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Data.Fintype.EquivFin

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit
set_option autoImplicit false
universe u
namespace MME.RecursiveYZ.Certificate

noncomputable def Stage.childCells {D : HashExtraction.HashData} (_A : Stage D) : ℕ :=
  Fintype.card (Cell D.half D.R D.parent)

noncomputable def Stage.childCell {D : HashExtraction.HashData} (A : Stage D) :
    Fin A.childCells ≃ Cell D.half D.R D.parent :=
  (Fintype.equivFin _).symm

/-- Both halves of the parent contribute to the same intact child tensor. -/
noncomputable def Stage.childMultiplicity {D : HashExtraction.HashData} (A : Stage D)
    (j : Fin A.childCells) : ℕ :=
  let c := A.childCell j
  D.m c.1 c.2 + D.m c.1 (complement (A.total c.1) c.2)

noncomputable def Stage.childTensor {D : HashExtraction.HashData} (A : Stage D)
    (K : Type u) [Field K] (j : Fin A.childCells) : TensorObj K 3 :=
  let c := A.childCell j
  unbroken K 5 A.ell (A.childMultiplicity j) (Equiv.refl _) (fun _ ↦ Unit.unit)
    (fun _ i ↦ (c.2.val i).val) (fun i _ ↦ A.mu i c)

/-- Actual finite child extractions. The enclosing intact-template conversion is not assumed. -/
structure Stage.ChildMM {D : HashExtraction.HashData} (A : Stage D)
    (K : Type u) [Field K] where
  a : Fin A.childCells → ℕ
  b : Fin A.childCells → ℕ
  c : Fin A.childCells → ℕ
  extract : ∀ j, TensorObj.Restrict (MMObj K (a j) (b j) (c j)) (A.childTensor K j)

noncomputable def Stage.ChildMM.dimA {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (M : A.ChildMM K) : ℕ := ∏ j, M.a j
noncomputable def Stage.ChildMM.dimB {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (M : A.ChildMM K) : ℕ := ∏ j, M.b j
noncomputable def Stage.ChildMM.dimC {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (M : A.ChildMM K) : ℕ := ∏ j, M.c j

end MME.RecursiveYZ.Certificate


