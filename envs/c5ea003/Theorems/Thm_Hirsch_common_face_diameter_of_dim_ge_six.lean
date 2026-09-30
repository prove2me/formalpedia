-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_ge_six
-- name    : Hirsch.common_face_diameter_of_dim_ge_six
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T03:30:15.376839+00:00
-- url     : https://prove2.me/theorems/87a8b4f4-8b58-4340-8cb9-5fd1b548d01e
-- title:
--   Polynomial diameter of common faces of dimension at least six
-- statement:
--   Polynomial combinatorial diameter of a common face of dimension at least six.
--
--   Dimension five is already polynomial via Larman (budget 4n). This statement isolates the remaining uniform-in-dimension content. Larman n 2^{h-3} and Kalai--Kleitman are the wrong growth for a single pair C,k independent of dimension.
--
--   **Formalization Note** Walks are padded.
-- source:
--   Restriction of Hirsch.common_face_diameter_of_dim_ge_five after the h=5 Larman specialization. Complementary case Hirsch.common_face_diameter_of_dim_eq_five (Proved, budget 4n).

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_ge_six :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (u x : EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded (Hpoly a b) →
      6 ≤ HirschCommonFace.commonFaceDim a b u x →
      (HirschCommonFace.commonFace a b u x).Nonempty →
      DiamLE (HirschCommonFace.commonFace a b u x) (C * (n + d) ^ k) := by sorry

end Hirsch
