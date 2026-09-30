-- Prove2me | Theorems.Thm_Hirsch_given_supporting_face_access_of_boundary_residual_rank
-- name    : Hirsch.given_supporting_face_access_of_boundary_residual_rank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T19:43:30.539692+00:00
-- url     : https://prove2.me/theorems/7eeb1ee6-c837-4814-943c-2d39cf6fc4a7
-- title:
--   Prescribed supporting-face access under a boundary-local residual-rank bound
-- statement:
--   Let P be a bounded H-polytope described by n inequalities, with vertices u,v. Fix a describing row i tight at v. At every edge x-z entering its supporting face from outside, let C_x be the span of normals tight at both u and x. Assume that every nonzero normal active at x but not at u belongs to K+C_x for some subspace K of dimension at most r. K may depend on x,z. Then an extreme point on THAT prescribed supporting face is reachable from u in at most n*2^max(r-3,0)+1 padded edge steps. Components in the common normal span are free; other newly active target rows are not excluded. The condition is required only at predecessors of boundary-crossing edges. No endpoint separation or distinctness is needed. This is a restricted access theorem, not a proof of the unconditional polynomial Hirsch leaf.
-- source:
--   Working result for the Polynomial Hirsch mission, September 2026. Exact checked source in jjoshua2/prove2me-work, branch chatgpt/prescribed-face-rank. No literature-priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.given_supporting_face_access_of_boundary_residual_rank
    (d n r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (i : Fin n) (hiv : ⟪a i, v⟫ = b i)
    (hboundary : ∀ x z, Adj (Hpoly a b) x z →
      ⟪a i, x⟫ ≠ b i → ⟪a i, z⟫ = b i →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ j, a j ≠ 0 → ⟪a j, x⟫ = b j → ⟪a j, u⟫ ≠ b j →
          a j ∈ K ⊔ Submodule.span ℝ
            (a '' {k | ⟪a k, u⟫ = b k ∧ ⟪a k, x⟫ = b k})) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < n * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry
