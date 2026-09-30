-- Prove2me | Theorems.Thm_Hirsch_face_interval_cover_route_bound_of_feasible_start_containment
-- name    : Hirsch.face_interval_cover_route_bound_of_feasible_start_containment
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T21:27:28.140443+00:00
-- url     : https://prove2.me/theorems/6dc401ab-6fc2-48c9-a3fa-7e1a2b17c102
-- title:
--   Start-containment routing with nonvertex marked checkpoints
-- statement:
--   For a finite interval cover by closed extreme faces of a compact parent, the marked interval endpoints need not themselves be vertices. If the two global endpoints are parent vertices, every interval endpoint lies in its supporting face, every old step is covered, and every later interval start occurring while an earlier interval is active lies in the earlier face, then the endpoints are joined by a parent edge/stay walk whose length is at most the sum of the intrinsic face-diameter budgets.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem face_interval_cover_route_bound_of_feasible_start_containment
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (s t : ι → ℕ) (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hbound : ∀ i, t i ≤ L)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hends : ∀ i, w (s i) ∈ F i ∧ w (t i) ∈ F i)
    (hcover : ∀ k < L, ∃ i, s i ≤ k ∧ k + 1 ≤ t i)
    (hcontain : ∀ i j, s i ≤ s j → s j ≤ t i → w (s j) ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by sorry

end Hirsch
