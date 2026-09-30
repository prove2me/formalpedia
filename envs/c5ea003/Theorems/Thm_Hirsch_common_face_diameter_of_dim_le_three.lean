-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_le_three
-- name    : Hirsch.common_face_diameter_of_dim_le_three
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T01:39:57.444336+00:00
-- url     : https://prove2.me/theorems/a894cfcb-9e61-4b5d-8805-1d767ada3cb0
-- title:
--   Klee diameter bound for common faces of dimension at most three
-- statement:
--   A common face of dimension at most three has combinatorial diameter at most the number of describing rows minus that dimension.
--
--   Let $P\subseteq\mathbb{R}^d$ be a bounded H-polytope cut out by $n$ linear inequalities, and let $F=F(u,x)$ be the face of $P$ obtained by imposing equality in every nonzero describing row tight at both $u$ and $x$. Write $h$ for the dimension of the corresponding common-direction space. If $F$ is nonempty and
--
--   $$
--   h\le 3,
--   $$
--
--   then
--
--   $$
--   \operatorname{DiamLE}(F,\,n-h).
--   $$
--
--   The bound is Klee's theorem applied in the canonical orthonormal coordinates on the common-direction space, then transported back along the affine isometry $q\mapsto u+Lq$. Edges of the coordinate H-polytope map to edges of $F$. No irredundancy or strict-feasibility hypothesis is used. The result does not bound the diameter of a common face of dimension four or more, and it does not by itself prove polynomial circuit-to-edge refinement: a circuit step may still have $h\ge 4$.
--
--   **Formalization Note** The Lean statement uses the public vocabulary `HirschCommonFace.commonFace` and `commonFaceDim`. Natural subtraction is truncated, so the budget is zero when $n<h$. Walks are padded.
-- source:
--   Klee's theorem in ambient dimension at most three (Prove2Me Hirsch.dimension_three_bound; V. Klee, Convex polytopes and linear programming, Proc. IBM Sci. Comput. Symp. Combin. Probl. 1966), applied to the canonical common-face coordinate H-presentation from Definitions.Def_Hirsch_common_face_geometry. Affine transport of extreme segments is the standard fact that an injective affine map preserves 1-extreme sets.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_le_three
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hdim : HirschCommonFace.commonFaceDim a b u x ≤ 3)
    (hne : (HirschCommonFace.commonFace a b u x).Nonempty) :
    DiamLE (HirschCommonFace.commonFace a b u x)
      (n - HirschCommonFace.commonFaceDim a b u x) := by sorry

end Hirsch
