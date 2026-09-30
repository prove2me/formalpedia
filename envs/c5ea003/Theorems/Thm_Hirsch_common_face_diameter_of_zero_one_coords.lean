-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_zero_one_coords
-- name    : Hirsch.common_face_diameter_of_zero_one_coords
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T06:51:43.160504+00:00
-- url     : https://prove2.me/theorems/d7d477d7-7f72-46da-961b-a906cde843ab
-- title:
--   A common face with $0/1$ coordinate vertices has diameter at most its dimension
-- statement:
--   **Naddef on a common face with $0/1$ coordinates.** Let $P$ be a bounded H-polytope in $\mathbb{R}^d$, and let $F$ be the common face of two points $u,x\in P$, of intrinsic dimension $h$. Write $Q$ for the canonical coordinate H-polytope of $F$ in $\mathbb{R}^h$. If every extreme point of $Q$ has coordinates in $\{0,1\}$, then the vertex-edge graph of $F$ has padded combinatorial diameter at most $h$.
--
--   The coordinate polytope is bounded because $F\subseteq P$ is bounded and the coordinate chart is an affine isometry. Naddef's theorem then gives $\mathrm{DiamLE}(Q,h)$, and the already-proved coordinate transfer lifts that bound to $F$.
--
--   This is a restricted-family theorem: it applies only when the coordinate vertices are $0/1$. It does not close the unrestricted common-face diameter leaf of dimension $\ge 6$, and it does not prove the polynomial Hirsch conjecture.
-- source:
--   Naddef, Math. Programming 45 (1989), applied in the canonical coordinates of a HirschCommonFace; transfer via Hirsch.common_face_diamLE_of_coord_diamLE and Hirsch.zero_one_polytope_diameter_le_dimension.

import Mathlib
import Definitions.Def_Hirsch_common_face_geometry
set_option autoImplicit false
open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem common_face_diameter_of_zero_one_coords
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (h01 : ∀ q ∈ Set.extremePoints ℝ
        (Hpoly (HirschCommonFace.commonFaceA a b u x)
          (HirschCommonFace.commonFaceB a b u x)),
      ∀ i : Fin (HirschCommonFace.commonFaceDim a b u x),
        q i = 0 ∨ q i = 1) :
    DiamLE (HirschCommonFace.commonFace a b u x)
      (HirschCommonFace.commonFaceDim a b u x) := by sorry

end Hirsch
