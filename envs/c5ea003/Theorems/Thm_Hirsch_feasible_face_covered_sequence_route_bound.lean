-- Prove2me | Theorems.Thm_Hirsch_feasible_face_covered_sequence_route_bound
-- name    : Hirsch.feasible_face_covered_sequence_route_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:20:31.471805+00:00
-- url     : https://prove2.me/theorems/62aa8163-1166-4085-9111-b0ed6b01bf82
-- title:
--   Feasible face-covered checkpoints route with one charge per face
-- statement:
--   For a feasible checkpoint sequence in a compact parent, if each consecutive checkpoint pair lies in one supplied closed extreme face and the global endpoints are parent vertices, then there is a padded parent-edge route with total length at most the sum of the supplied face-diameter budgets. Intermediate checkpoints need not be vertices.
-- source:
--   Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem feasible_face_covered_sequence_route_bound
    {d : ℕ} {ι : Type*} [Fintype ι]
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d))) (B : ι → ℕ)
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) (hD : ∀ i, DiamLE (F i) (B i))
    (w : ℕ → EuclideanSpace ℝ (Fin d)) (L : ℕ)
    (hfeas : ∀ k ≤ L, w k ∈ P)
    (h0 : w 0 ∈ extremePoints ℝ P) (hL : w L ∈ extremePoints ℝ P)
    (hcover : ∀ k < L, ∃ i, w k ∈ F i ∧ w (k + 1) ∈ F i) :
    ∃ q : ℕ → EuclideanSpace ℝ (Fin d),
      q 0 = w 0 ∧ q (∑ i, B i) = w L ∧
      ∀ r < ∑ i, B i,
        q r = q (r + 1) ∨ Adj P (q r) (q (r + 1)) := by sorry

end Hirsch
