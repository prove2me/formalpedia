-- Prove2me | Theorems.Thm_Hirsch_rank_selected_row_face_diameter_bound
-- name    : Hirsch.rank_selected_row_face_diameter_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T23:25:48.972775+00:00
-- url     : https://prove2.me/theorems/76cdff62-bb43-4758-a1ed-980ce0ec5230
-- title:
--   Rank-selected supporting sections bound an extreme face diameter
-- statement:
--   Let $F$ be an extreme subset of an $n$-row H-polyhedron in $\mathbb R^d$, with connected vertex-edge graph. Let $U$ be any row-normal subspace of rank $r<d$. For each row with $a_i\notin U$, assume intrinsic padded diameter at most $B_i$ for
--   $$F_i=F\cap\{x\in P:\langle a_i,x\rangle=b_i\}.$$
--   Then
--   $$\operatorname{diam}(F)\le\left\lfloor\frac{\sum_{a_i\notin U}(B_i+1)}{d-r}\right\rfloor-1,$$
--   with truncated natural subtraction and the padded-walk convention. Rows in $U$ are neither charged nor assumed to have any diameter bound. This theorem does not assert that the selected sections are proper for an arbitrary $U$, or that their supplied budgets are small. Proper descent requires separately choosing a saturated normal space.
-- source:
--   https://github.com/jjoshua2/prove2me-work/blob/681314640b6f84792d8ae011c3534a6e8c456930/Solutions/PolynomialRankSensitiveFaceCover.lean ; declaration HirschRankFaceCover.diamLE_of_rank_increasing_row_bounds; pinned CI run 34532572816.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace Hirsch

theorem rank_selected_row_face_diameter_bound {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (F : Set (EuclideanSpace ℝ (Fin d))) (hF : IsExtreme ℝ (Hpoly a b) F)
    (U : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hU : Module.finrank ℝ U < d)
    (B : Fin n → ℕ)
    (hFD : ∀ i, a i ∉ U →
      DiamLE (F ∩ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i}) (B i))
    (hconnect : ∀ u ∈ extremePoints ℝ F, ∀ v ∈ extremePoints ℝ F,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj F (w j) (w (j + 1))) :
    DiamLE F
      ((∑ i ∈ Finset.univ.filter (fun i => a i ∉ U), (B i + 1)) /
        (d - Module.finrank ℝ U) - 1) := by sorry

end Hirsch
