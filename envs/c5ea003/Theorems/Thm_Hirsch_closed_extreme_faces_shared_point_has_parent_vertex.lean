-- Prove2me | Theorems.Thm_Hirsch_closed_extreme_faces_shared_point_has_parent_vertex
-- name    : Hirsch.closed_extreme_faces_shared_point_has_parent_vertex
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:17:31.541098+00:00
-- url     : https://prove2.me/theorems/927effb2-313a-485a-b121-7e2cba51c753
-- title:
--   Intersecting closed extreme faces of a compact parent share a parent vertex
-- statement:
--   If two closed extreme faces of a compact Euclidean parent share any point, even a nonvertex point, they share a parent extreme vertex.
-- source:
--   Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem closed_extreme_faces_shared_point_has_parent_vertex
    {d : ℕ} (P F G : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hG : IsExtreme ℝ P G)
    (hFc : IsClosed F) (hGc : IsClosed G)
    (x : EuclideanSpace ℝ (Fin d)) (hxF : x ∈ F) (hxG : x ∈ G) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F ∧ v ∈ G := by sorry

end Hirsch
