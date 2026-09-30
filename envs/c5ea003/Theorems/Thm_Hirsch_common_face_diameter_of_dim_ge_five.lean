-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_ge_five
-- name    : Hirsch.common_face_diameter_of_dim_ge_five
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T02:46:27.743295+00:00
-- url     : https://prove2.me/theorems/495d8bd4-50b7-44d8-9c70-f75a7ad55a87
-- title:
--   Polynomial diameter of common faces of dimension at least five
-- statement:
--   Polynomial combinatorial diameter of a common face of dimension at least five.
--
--   There exist C,k such that every nonempty common face of common-direction dimension h\ge 5 in a bounded n-row d-polytope has DiamLE at most C(n+d)^k. Dimension four is already polynomial via Larman (budget 2n). This statement is the remaining uniform-in-dimension content of polynomial Hirsch. Kalai--Kleitman and the full Larman bound n 2^{h-3} are the wrong growth for a single pair C,k independent of d.
--
--   **Formalization Note** Walks are padded.
-- source:
--   Restriction of Hirsch.common_face_diameter_of_dim_ge_four to common-face dimension at least five. Complementary dimension-four case: Larman in 4-dimensional coordinates, budget 2n.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_ge_five :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (u x : EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded (Hpoly a b) →
      5 ≤ HirschCommonFace.commonFaceDim a b u x →
      (HirschCommonFace.commonFace a b u x).Nonempty →
      DiamLE (HirschCommonFace.commonFace a b u x) (C * (n + d) ^ k) := by sorry

end Hirsch
