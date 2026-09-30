-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_effective_rows
-- name    : Hirsch.common_face_diameter_of_effective_rows
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T11:28:02.621557+00:00
-- url     : https://prove2.me/theorems/496bd99b-f3dc-465e-9c99-ebca0b1129be
-- title:
--   Transfer a balanced diameter theorem to a common face with few effective rows
-- statement:
--   If the canonical coordinate H-presentation of a common face has at most twice its dimension many nonzero restricted row normals, then any uniform diameter theorem for exactly balanced presentations of that dimension applies to the common face.
-- source:
--   Verified effective-row common-face model from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #28.

import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem common_face_diameter_of_effective_rows
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : HirschCommonFace.commonFaceEffectiveCount a b u x ≤
      2 * HirschCommonFace.commonFaceDim a b u x)
    (hbalanced : ∀
      (a' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) →
        EuclideanSpace ℝ (Fin (HirschCommonFace.commonFaceDim a b u x)))
      (b' : Fin (2 * HirschCommonFace.commonFaceDim a b u x) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (HirschCommonFace.commonFaceA a b u x)
      (HirschCommonFace.commonFaceB a b u x)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x))) :
    DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B := by sorry

end Hirsch
