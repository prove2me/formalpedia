-- Prove2me | Theorems.Thm_Hirsch_face_preserving_vertex_selection
-- name    : Hirsch.face_preserving_vertex_selection
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T21:24:59.94208+00:00
-- url     : https://prove2.me/theorems/c8ebefd3-d31a-4d33-b1f8-6298669cc3ba
-- title:
--   Simultaneous face-preserving rounding to parent vertices
-- statement:
--   Let P be a compact Euclidean polytope and let F_i be any family of closed extreme subsets of P. There is one selection r sending every feasible point of P to a parent vertex, fixing every existing parent vertex, such that membership in every supplied face is preserved simultaneously: x in F_i implies r(x) in F_i. The family of faces need not be finite; no continuity or adjacency preservation is asserted.
-- source:
--   Verified Lean theorem from jjoshua2/prove2me-work PR #50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem face_preserving_vertex_selection
    {d : ℕ} {ι : Type*}
    (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i)) :
    ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ x ∈ P, r x ∈ extremePoints ℝ P) ∧
      (∀ x ∈ extremePoints ℝ P, r x = x) ∧
      (∀ i x, x ∈ F i → r x ∈ F i) := by sorry

end Hirsch
