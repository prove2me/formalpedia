-- Prove2me | Theorems.Thm_Hirsch_closed_extreme_faces_disjoint_of_no_shared_parent_extreme
-- name    : Hirsch.closed_extreme_faces_disjoint_of_no_shared_parent_extreme
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-12T14:41:58.163749+00:00
-- url     : https://prove2.me/theorems/28f797e1-c7bd-49fd-b3b5-570c22329bdc
-- title:
--   Closed extreme faces with no shared parent extreme point are disjoint
-- statement:
--   Let P be a compact subset of finite-dimensional Euclidean space, and let F and G be closed extreme subsets of P. If no extreme point of P belongs to both F and G, then F and G are disjoint. Equivalently, any nonempty intersection of two closed extreme faces of a compact parent contains a parent extreme point.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/fb1594e865b723ea2e6bf63baf46beeba7025027 ; standalone Lean/Axiom gate Actions run 34699009349

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
open scoped RealInnerProductSpace
open Set

namespace Hirsch
theorem closed_extreme_faces_disjoint_of_no_shared_parent_extreme
    {d : ℕ}
    (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P)
    (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (hno : ¬ ∃ v : EuclideanSpace ℝ (Fin d),
      v ∈ Set.extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G) :
    Disjoint F G := by sorry
end Hirsch
