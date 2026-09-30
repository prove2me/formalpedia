-- Prove2me | Theorems.Thm_Hirsch_cut_face_access_of_unbounded_outer_diameter
-- name    : Hirsch.cut_face_access_of_unbounded_outer_diameter
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-07T02:43:01.167465+00:00
-- url     : https://prove2.me/theorems/12f145c8-ecde-4cdd-97b2-eb9b24d1d778
-- title:
--   Specified cut-face access with a possibly unbounded outer H-polyhedron
-- statement:
--   Let Q be an H-polyhedron described by n inequalities in R^d and P=Q intersect {x:<c,x><=beta}. Assume P is bounded and the vertex-edge graph of Q has diameter at most B. For every two extreme points u,v of P with <c,v>=beta, some extreme point z of P on the SAME specified cut plane is reachable from u by at most B+1 edges. Q need not be bounded, and no outer extreme point on or beyond the cut plane is required. No nonzero-normal or full-dimensionality hypothesis is imposed. Larman is used only for connectivity of the bounded (n+1)-row clip; its numerical bound is discarded. This does not promise reaching v or establish a uniform polynomial outer-graph diameter bound.
-- source:
--   Working theorem for the Polynomial Hirsch mission; jjoshua2/prove2me-work, branch chatgpt/unbounded-cut-routing. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.cut_face_access_of_unbounded_outer_diameter
    (d n B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (β : ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hQ : DiamLE (Hpoly a b) B)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hv : v ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}))
    (hvc : ⟪c, v⟫ = β) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) ∧
      ⟪c, z⟫ = β ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨
            Adj (Hpoly a b ∩ {x | ⟪c, x⟫ ≤ β}) (w j) (w (j + 1)) := by sorry
