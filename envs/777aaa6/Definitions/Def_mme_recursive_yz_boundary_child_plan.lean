-- Prove2me | Definitions.Def_mme_recursive_yz_boundary_child_plan
-- name    : mme_recursive_yz_boundary_child_plan
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-13T12:51:54.387744+00:00
-- url     : https://prove2.me/theorems/9993e5db-110e-4c99-8cd1-9ffed39aa668
-- title:
--   Recursive child data with constructed boundary cases
-- statement:
--   For each literal recursive child tensor, record its proposed matrix dimensions. A boundary child is specified by exact equality of its grades and full integer profiles with a boundary profile, together with the explicit dimension formula; no boundary tensor map is an input. An interior child must have all three grades strictly positive and supply its actual matrix restriction. Products of the proposed dimensions are recorded for use in the same cofinal witness.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6, Remark 6.1, Theorem 6.2 and subsequent separation of boundary and interior terms.

import Definitions.Def_mme_recursive_yz_boundary_data
open BigOperators MME MME.TensorObj MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary
set_option autoImplicit false
universe u
namespace MME.RecursiveYZ.Certificate

/-- Scalar profile and shape identifications for a boundary child. There is no tensor-map input. -/
def Stage.BoundaryChild {D : HashExtraction.HashData} (A : Stage D)
    (j : Fin A.childCells) (a b c : ℕ) : Prop :=
  ∃ z : Fin 3, ∃ B : Boundary.Profile A.ell (A.childMultiplicity j),
    (∀ i, ((A.childCell j).2.val i).val = B.shape z i) ∧
    (∀ i, A.mu i (A.childCell j) = B.mu z i) ∧
    a = B.a z ∧ b = B.b z ∧ c = B.c z

/-- Boundary maps are supplied by the exact-profile theorem; only interior maps remain inputs. -/
structure Stage.ChildPlan {D : HashExtraction.HashData} (A : Stage D)
    (K : Type u) [Field K] where
  a : Fin A.childCells → ℕ
  b : Fin A.childCells → ℕ
  c : Fin A.childCells → ℕ
  cases : ∀ j,
    A.BoundaryChild j (a j) (b j) (c j) ∨
    ((∀ i, 0 < ((A.childCell j).2.val i).val) ∧
      TensorObj.Restrict (MMObj K (a j) (b j) (c j)) (A.childTensor K j))

noncomputable def Stage.ChildPlan.dimA {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (P : A.ChildPlan K) : ℕ := ∏ j, P.a j
noncomputable def Stage.ChildPlan.dimB {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (P : A.ChildPlan K) : ℕ := ∏ j, P.b j
noncomputable def Stage.ChildPlan.dimC {D : HashExtraction.HashData} {A : Stage D}
    {K : Type u} [Field K] (P : A.ChildPlan K) : ℕ := ∏ j, P.c j

end MME.RecursiveYZ.Certificate


