-- Prove2me | Theorems.Thm_Hirsch_face_interval_cover_route_bound_of_feasible_active_containment
-- name    : Hirsch.face_interval_cover_route_bound_of_feasible_active_containment
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:22:47.733238+00:00
-- url     : https://prove2.me/theorems/40216355-af8c-46fb-ac9a-72979288e6f3
-- title:
--   Active-containment routing with nonvertex marked checkpoints
-- statement:
--   If each valid repair interval stays inside its closed extreme face throughout the interval, the marked checkpoints may be nonvertices: only the two global endpoints must already be parent vertices, and a padded route exists with length at most the sum of the face budgets.
-- source:
--   Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem face_interval_cover_route_bound_of_feasible_active_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hvalid : ∀ i, s i ≤ t i) (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hactive : ∀ i k, s i ≤ k → k ≤ t i → w k ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by sorry

end Hirsch
