-- Prove2me | Theorems.Thm_Hirsch_separated_common_face_split
-- name    : Hirsch.separated_common_face_split
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:26:21.889824+00:00
-- url     : https://prove2.me/theorems/b03857f7-3d18-4f3c-a6f8-213cb0d5d012
-- title:
--   Separated common-face splitter from lower-dimensional diameter control
-- statement:
--   For separated extreme endpoints u and v of a bounded n-row d-dimensional H-polytope, fix 1 <= R <= d. If every bounded nonempty n-row H-polytope in dimensions at most R-1 has padded graph diameter at most B, and u and v are connected, then within B+1 parent edge/stay steps from u one can reach an extreme vertex z whose common-face dimension with v is at most d + (n-2d) - R. In the balanced case n=2d this reaches common-face dimension at most d-R.
-- source:
--   Verified separated common-face splitter from jjoshua2/prove2me-work PR #30.

import Definitions.Def_Hirsch_common_face_geometry

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem separated_common_face_split
    (d n R B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hR0 : 1 ≤ R) (hRd : R ≤ d)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨
        Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ R - 1 →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      HirschCommonFace.commonFaceDim a b v z ≤ d + (n - 2 * d) - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
