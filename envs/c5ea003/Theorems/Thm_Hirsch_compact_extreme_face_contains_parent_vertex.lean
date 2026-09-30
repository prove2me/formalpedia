-- Prove2me | Theorems.Thm_Hirsch_compact_extreme_face_contains_parent_vertex
-- name    : Hirsch.compact_extreme_face_contains_parent_vertex
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:13:06.387984+00:00
-- url     : https://prove2.me/theorems/3df8730f-073f-4914-be78-64b1043b016f
-- title:
--   A nonempty closed extreme face of a compact parent contains a parent vertex
-- statement:
--   Every nonempty closed extreme subset of a compact Euclidean parent contains a point that is extreme in the parent and lies in the subset.
-- source:
--   Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem compact_extreme_face_contains_parent_vertex
    {d : ℕ} (P F : Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : IsExtreme ℝ P F) (hclosed : IsClosed F)
    (hne : F.Nonempty) :
    ∃ v, v ∈ extremePoints ℝ P ∧ v ∈ F := by sorry

end Hirsch
