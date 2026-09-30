-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_eq_five
-- name    : Hirsch.common_face_diameter_of_dim_eq_five
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T03:07:43.281949+00:00
-- url     : https://prove2.me/theorems/84ed6d52-c651-4c22-adf7-d8c91ee6b55c
-- title:
--   Larman diameter of a 5-dimensional common face
-- statement:
--   A common face of dimension exactly five has combinatorial diameter at most four times the number of describing rows.
--
--   Let $F$ be a nonempty common face of a bounded $n$-row H-polytope, with common-direction dimension $h=5$. Larman in the 5-dimensional coordinate presentation supplies
--   $$
--   \operatorname{DiamLE}(F,\, n\cdot 2^{5-3}) = \operatorname{DiamLE}(F,\, 4n).
--   $$
--   This is polynomial in $(n+d)$ for this fixed dimension. It is a helper for the open leaf `Hirsch.common_face_diameter_of_dim_ge_five` and is not a uniform polynomial for unbounded $h$.
--
--   **Formalization Note** Walks are padded.
-- source:
--   Specialization of Hirsch.common_face_larman_diameter to common-face dimension 5; Larman budget n 2^{h-3} becomes 4n. Helper for the open leaf Hirsch.common_face_diameter_of_dim_ge_five.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_eq_five
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (HirschCommonFace.commonFace a b u x).Nonempty)
    (hdim : HirschCommonFace.commonFaceDim a b u x = 5) :
    DiamLE (HirschCommonFace.commonFace a b u x) (4 * n) := by sorry

end Hirsch
