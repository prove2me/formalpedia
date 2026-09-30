-- Prove2me | Theorems.Thm_Hirsch_common_face_diamLE_of_coord_diamLE
-- name    : Hirsch.common_face_diamLE_of_coord_diamLE
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T03:48:52.806488+00:00
-- url     : https://prove2.me/theorems/d7b5f979-eb85-47c4-8c1d-a53aff0bccbe
-- title:
--   Common-face diameter transfers from coordinate H-polytopes
-- statement:
--   Graph diameter of a common face equals the graph diameter of its canonical coordinate H-polytope.
--
--   If the coordinate presentation in the common-direction space has $\operatorname{DiamLE}(Q,B)$, then the common face $F$ in the original ambient space has $\operatorname{DiamLE}(F,B)$. The coordinate map $q\mapsto u+Lq$ is an injective affine isometry onto $F$ and sends extreme segments to extreme segments. This transfers any budget, including a hypothetical uniform polynomial, from an $h$-dimensional H-polytope onto the face. It does not itself produce a polynomial bound.
--
--   **Formalization Note** No boundedness or dimension hypothesis is required beyond the coordinate DiamLE assumption.
-- source:
--   Affine transport of extreme segments along the public common-face coordinate isometry. Helper for Hirsch.common_face_diameter_of_dim_ge_six: a uniform polynomial on h-dimensional H-polytopes would transfer to the face.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diamLE_of_coord_diamLE
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hcoord : DiamLE
      (Hpoly (HirschCommonFace.commonFaceA a b u x)
        (HirschCommonFace.commonFaceB a b u x)) B) :
    DiamLE (HirschCommonFace.commonFace a b u x) B := by sorry

end Hirsch
