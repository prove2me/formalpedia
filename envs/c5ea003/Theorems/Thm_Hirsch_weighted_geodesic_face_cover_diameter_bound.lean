-- Prove2me | Theorems.Thm_Hirsch_weighted_geodesic_face_cover_diameter_bound
-- name    : Hirsch.weighted_geodesic_face_cover_diameter_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T22:14:08.755993+00:00
-- url     : https://prove2.me/theorems/7815b37c-dab5-42b8-a1ed-fbb08d1eab5b
-- title:
--   Weighted extreme-face covers bound graph diameter
-- statement:
--   Let $P\subseteq\mathbb R^d$ have connected vertex-edge graph, with adjacency defined by extreme line segments. Let $(F_i)$ be a finite family of extreme subsets of $P$, with nonnegative integer weights $w_i$ and integer budgets $B_i$. Assume every vertex receives total covering weight at least $q>0$, and assume intrinsic padded graph diameter at most $B_i$ only for those $F_i$ with positive weight. Then the padded graph diameter of $P$ is at most
--   $$\left\lfloor\frac{\sum_i w_i(B_i+1)}q\right\rfloor-1.$$
--   Natural-number subtraction is truncated at zero. Zero-weight sets have no diameter hypothesis or cost. No boundedness, polyhedral presentation, simplicity, or nonemptiness is required beyond the displayed hypotheses. This is a conditional certificate, not a claim that a cheap cover always exists.
-- source:
--   https://github.com/jjoshua2/prove2me-work/blob/681314640b6f84792d8ae011c3534a6e8c456930/Solutions/PolynomialWeightedFaceCover.lean ; declaration HirschFaceSplice.diamLE_of_weighted_face_cover; pinned CI run 34532572816.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 12000000

namespace Hirsch

theorem weighted_geodesic_face_cover_diameter_bound {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B weight : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, 0 < weight i → DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ ∑ i, if x ∈ F i then weight i else 0)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, weight i * (B i + 1)) / q - 1) := by sorry

end Hirsch
