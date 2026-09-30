-- Prove2me | Theorems.Thm_Hirsch_common_face_larman_diameter
-- name    : Hirsch.common_face_larman_diameter
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:43:02.880821+00:00
-- url     : https://prove2.me/theorems/acaf00eb-3d5b-402a-8bf2-78d20fdcda9d
-- title:
--   Larman diameter bound on a common face
-- statement:
--   Larman's bound on a common face: if F is a nonempty common face of a bounded n-row H-polytope, of common-direction dimension h, then DiamLE(F, n 2^{h-3}).
--
--   This is Larman's theorem applied in the canonical orthonormal coordinates of the common-direction space, then transported along the affine isometry onto F. It is exponential in h, not a uniform polynomial in (n+d).
--
--   **Formalization Note** Natural subtraction is truncated, so the exponent is zero when h<3.
-- source:
--   Hirsch.larman_bound applied to the common-face coordinate H-presentation from Definitions.Def_Hirsch_common_face_geometry. Affine transport of extreme segments.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_larman_diameter
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (HirschCommonFace.commonFace a b u x).Nonempty) :
    DiamLE (HirschCommonFace.commonFace a b u x)
      (n * 2 ^ (HirschCommonFace.commonFaceDim a b u x - 3)) := by sorry

end Hirsch
