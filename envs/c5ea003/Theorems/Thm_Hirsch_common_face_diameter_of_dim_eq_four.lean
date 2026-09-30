-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_eq_four
-- name    : Hirsch.common_face_diameter_of_dim_eq_four
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T02:55:09.655048+00:00
-- url     : https://prove2.me/theorems/4d800908-1011-4584-8625-fc4b095009fc
-- title:
--   Klee–Larman diameter of a 4-dimensional common face
-- statement:
--   A common face of dimension exactly four has combinatorial diameter at most twice the number of describing rows.
--
--   Let $F$ be a nonempty common face of a bounded $n$-row H-polytope, with common-direction dimension $h=4$. Larman in the 4-dimensional coordinate presentation supplies
--   $$
--   \operatorname{DiamLE}(F,\, n\cdot 2^{4-3}) = \operatorname{DiamLE}(F,\, 2n).
--   $$
--   This is polynomial in $(n+d)$. It does not bound faces of dimension five or more by a uniform polynomial.
--
--   **Formalization Note** Walks are padded.
-- source:
--   Specialization of Hirsch.common_face_larman_diameter to common-face dimension 4; Larman budget n 2^{h-3} becomes 2n.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_eq_four
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b))
    (hne : (HirschCommonFace.commonFace a b u x).Nonempty)
    (hdim : HirschCommonFace.commonFaceDim a b u x = 4) :
    DiamLE (HirschCommonFace.commonFace a b u x) (2 * n) := by sorry

end Hirsch
