-- Prove2me | Theorems.Thm_Hirsch_common_face_dimension_tradeoff
-- name    : Hirsch.common_face_dimension_tradeoff
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T11:22:27.043997+00:00
-- url     : https://prove2.me/theorems/b56b59cc-fe2a-4d64-979d-595cabec37ca
-- title:
--   Common-face dimensions overlap only through row excess
-- statement:
--   For separated extreme endpoints u and v of an n-row H-polytope in dimension d, and any intermediate extreme vertex x, the dimensions of the common-direction spaces determined by (u,x) and (v,x) sum to at most d+(n-2d). In the balanced case n=2d they sum to at most d.
-- source:
--   Verified structural lemma from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #30.

import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem common_face_dimension_tradeoff
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    HirschCommonFace.commonFaceDim a b u x +
      HirschCommonFace.commonFaceDim a b v x ≤ d + (n - 2 * d) := by sorry

end Hirsch
