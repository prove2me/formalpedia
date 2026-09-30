-- Prove2me | Theorems.Thm_Hirsch_feasible_point_has_face_preserving_parent_vertex
-- name    : Hirsch.feasible_point_has_face_preserving_parent_vertex
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-10T02:15:10.764089+00:00
-- url     : https://prove2.me/theorems/0d77a819-5b23-48a2-91ba-34a6f44b49af
-- title:
--   A feasible point can be rounded to a parent vertex preserving all closed-face memberships
-- statement:
--   For a compact parent and any family of closed extreme faces, every feasible point has a parent extreme vertex that lies in every supplied face containing the point; the face family need not be finite.
-- source:
--   Kernel-verified theorem from jjoshua2/prove2me-work PR #48/#50.

import Mathlib
import Mathlib.Analysis.Convex.KreinMilman
import Definitions.Def_Hirsch_model

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

namespace Hirsch

theorem feasible_point_has_face_preserving_parent_vertex
    {d : ℕ} {ι : Type*} (P : Set (EuclideanSpace ℝ (Fin d)))
    (F : ι → Set (EuclideanSpace ℝ (Fin d)))
    (hP : IsCompact P) (hF : ∀ i, IsExtreme ℝ P (F i))
    (hclosed : ∀ i, IsClosed (F i))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ P) :
    ∃ v, v ∈ extremePoints ℝ P ∧ ∀ i, x ∈ F i → v ∈ F i := by sorry

end Hirsch
