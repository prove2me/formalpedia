-- Prove2me | Definitions.Def_Hirsch_common_face_geometry
-- name    : Hirsch_common_face_geometry
-- status  : Definition
-- author  : @jjosh
-- created : 2026-09-09T11:21:35.014221+00:00
-- url     : https://prove2.me/theorems/dc9161e6-0dae-4da5-ab82-91b871e2409e
-- title:
--   Common-face direction and coordinate geometry
-- statement:
--   Public definitions for common active rows, endpoint-neutral rows, common-direction kernels and dimensions, canonical common-face coordinates, effective restricted rows, and sparse subpresentations.
-- source:
--   Formalization infrastructure developed for the Polynomial Hirsch mission; definitions are standard finite-dimensional H-polytope linear algebra.

import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

noncomputable section

/- Public common-face vocabulary used by structural Polynomial Hirsch lemmas.
It includes the intrinsic direction-space definitions and the canonical
orthonormal coordinate H-presentation of the common face. -/
namespace HirschCommonFace

variable {d n : ℕ}

/-- Nonzero describing rows active at both points. -/
noncomputable def commonSourceRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i)

/-- Nonzero describing rows active at neither endpoint. -/
noncomputable def neutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ ≠ b i)

/-- Evaluate a direction against a selected finite set of row normals. -/
noncomputable def rowEvalMap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
  { toFun := fun y i => ⟪a i.1, y⟫
    map_add' := by
      intro y z
      funext i
      simp [inner_add_right]
    map_smul' := by
      intro c y
      funext i
      simp [inner_smul_right] }

/-- Directions annihilating every nonzero row active at both points. -/
noncomputable def commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (rowEvalMap a (commonSourceRows a b u x)).ker

/-- The parent H-polytope face cut out by all nonzero rows active at both
points. -/
noncomputable def commonFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ Hpoly a b ∧
    ∀ i, i ∈ commonSourceRows a b u x → ⟪a i, y⟫ = b i}

/-- Linear dimension of the common-direction space. -/
noncomputable def commonFaceDim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  Module.finrank ℝ (commonDirection a b u x)

/-- Canonical orthonormal coordinates on the common-direction space. -/
noncomputable def commonFaceRepr
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    commonDirection a b u x ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) := by
  simpa [commonFaceDim] using
    (stdOrthonormalBasis ℝ (commonDirection a b u x)).repr

/-- Isometric inclusion from common-face coordinates into the ambient
Euclidean direction space. -/
noncomputable def commonFaceLift
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonDirection a b u x).subtypeₗᵢ.comp
    (commonFaceRepr a b u x).symm.toLinearIsometry

noncomputable def commonFaceLiftCLM
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →L[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonFaceLift a b u x).toContinuousLinearMap

/-- Original row normal restricted to the common-direction space and written
in canonical orthonormal coordinates. -/
noncomputable def commonFaceA
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) :=
  ContinuousLinearMap.adjoint (commonFaceLiftCLM a b u x) (a i)

/-- Right-hand side of the translated common-face coordinate inequality. -/
noncomputable def commonFaceB
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  b i - ⟪a i, u⟫

/-- Lift a common-face coordinate point back to the ambient affine face. -/
noncomputable def commonFacePoint
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    EuclideanSpace ℝ (Fin d) :=
  u + commonFaceLift a b u x q

/-- Rows whose restricted normals remain nonzero in common-face coordinates. -/
noncomputable def commonFaceEffectiveRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => commonFaceA a b u x i ≠ 0)

noncomputable def commonFaceEffectiveCount
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (commonFaceEffectiveRows a b u x).card

/-- An H-presentation has an equivalent subpresentation using at most `M` of
its original rows. -/
def HasSubpresentationAtMost {r n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin r)) (b : Fin n → ℝ) (M : ℕ) : Prop :=
  ∃ m : ℕ, m ≤ M ∧ ∃ e : Fin m ↪ Fin n,
    Hpoly (fun j => a (e j)) (fun j => b (e j)) = Hpoly a b

/-- Sparse-presentation condition specialized to common-face coordinates. -/
def CommonFaceHasSubpresentationAtMost {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (M : ℕ) : Prop :=
  HasSubpresentationAtMost
    (commonFaceA a b p q) (commonFaceB a b p q) M

end HirschCommonFace


