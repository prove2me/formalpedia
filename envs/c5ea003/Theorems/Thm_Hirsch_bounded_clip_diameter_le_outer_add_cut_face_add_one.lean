-- Prove2me | Theorems.Thm_Hirsch_bounded_clip_diameter_le_outer_add_cut_face_add_one
-- name    : Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-07T02:46:38.927761+00:00
-- url     : https://prove2.me/theorems/376a6b61-a5a9-4c6f-87c6-4bddc9aa64b1
-- title:
--   Bounded clipped diameter is at most outer plus cut-face diameter plus one
-- statement:
--   Let Q be an H-polyhedron in R^d, P=Q intersect {x:<c,x><=beta}, and F=Q intersect {x:<c,x>=beta}. If P is bounded, DiamLE Q B, and DiamLE F C, then DiamLE P (B+C+1). Q may be unbounded. No exterior outer vertex, nonempty clip, nonempty cut face, nonzero normal, or full-dimensionality assumption is required. This covers all clipped vertices, including newly created ones. It transfers two assumed bounds and does not prove the unrestricted polynomial Hirsch conjecture.
-- source:
--   Working theorem for the Polynomial Hirsch mission; jjoshua2/prove2me-work, branch chatgpt/unbounded-cut-routing. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.bounded_clip_diameter_le_outer_add_cut_face_add_one
    (d n B C : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hQ : DiamLE (Hpoly a b) B)
    (hF : DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ = β}) C) :
    DiamLE (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) (B + C + 1) := by sorry
