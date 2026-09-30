-- Prove2me | Theorems.Thm_Hirsch_geodesic_face_cover_diameter_bound
-- name    : Hirsch.geodesic_face_cover_diameter_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T11:21:56.054046+00:00
-- url     : https://prove2.me/theorems/81bb9472-8b70-48dd-b7cc-1921d6a14fe9
-- title:
--   Extreme-face incidence cover bounds parent graph diameter
-- statement:
--   Let a connected vertex graph be covered by a finite family of extreme faces. If each vertex lies in at least q>0 selected faces and selected face i has intrinsic graph diameter at most B_i, then the parent padded diameter is at most (sum_i(B_i+1))/q - 1. The proof counts visits of a shortest path to faces and remains valid when the path leaves and later re-enters a face.
-- source:
--   Verified graph-geometry theorem from the Polynomial Hirsch formalization, jjoshua2/prove2me-work PR #27.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace BigOperators
open Set Hirsch
attribute [local instance] Classical.propDecidable

namespace Hirsch

theorem geodesic_face_cover_diameter_bound
    {ι : Type*} [Fintype ι]
    (d q : ℕ) (hq : 0 < q)
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hF : ∀ i, IsExtreme ℝ P (F i))
    (hFD : ∀ i, DiamLE (F i) (B i))
    (hcover : ∀ x ∈ extremePoints ℝ P,
      q ≤ (Finset.univ.filter (fun i => x ∈ F i)).card)
    (hconnect : ∀ u ∈ extremePoints ℝ P, ∀ v ∈ extremePoints ℝ P,
      ∃ L : ℕ, ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w L = v ∧
        ∀ j < L, w j = w (j + 1) ∨ Adj P (w j) (w (j + 1))) :
    DiamLE P ((∑ i, (B i + 1)) / q - 1) := by sorry

end Hirsch
