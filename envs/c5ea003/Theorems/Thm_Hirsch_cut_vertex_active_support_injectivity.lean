-- Prove2me | Theorems.Thm_Hirsch_cut_vertex_active_support_injectivity
-- name    : Hirsch.cut_vertex_active_support_injectivity
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-17T03:45:07.627929+00:00
-- url     : https://prove2.me/theorems/c3781e27-7eb2-4ffc-bb5b-e85ffe60c480
-- title:
--   Active cuts detect every affine motion in a positive support of a cut vertex
-- statement:
--   Let P be any convex subset of a finite-dimensional real coordinate space, let v_i be finitely many points of P, and let strictly positive weights w_i sum to one. Suppose their barycentre x is an extreme point of the actual intersection P with finitely many linear halfspaces C_j(y)<=b_j. Then every zero-total affine coefficient perturbation t_i whose geometric motion is annihilated by all cuts active at x has zero geometric motion. Consequently, if the homogenized support vectors (1,v_i) are linearly independent, their homogenized images (1,(C_j(v_i))_j) under the ACTIVE cuts are linearly independent too, and the number of support points is at most the number of active cuts plus one. The proof chooses a positive perturbation radius preserving every support weight and every inactive cut slack; convexity gives two feasible perturbed points, whose midpoint is x, so actual extremality forces the motion to vanish. No injectivity, active-rank, support-size, or optimizer oracle is assumed. Compactness, simplicity, independence of the cut normals, and support points being base vertices are not required. Strict positivity of support weights is necessary; zero-weight points can first be removed outside this statement. This local theorem does not itself construct a Caratheodory representation, the complete post-cut coordinate alphabet, a geometric edge walk, or a polynomial diameter bound for arbitrary polytopes.
-- source:
--   Geometric active-cut rank step used in research/CUT_VERTEX_LEVEL_CLOSURE.md Section 1 (merged #277). This is a standalone formalization of the finite perturbation argument, not a resubmission of the accepted finite_coordinate_extreme_route_bound or the separately owned moment-curve catalogue. Standard convex/linear algebra; no historical novelty claim. Mathlib convex sum membership, extremePoints, linear independence and dimension APIs are used at the committed repository pin. No internal namespace declarations occur in the target preamble.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem Hirsch.cut_vertex_active_support_injectivity
    (n m d : ℕ) (P : Set (Fin d → ℝ)) (hP : Convex ℝ P)
    (v : Fin n → Fin d → ℝ) (hv : ∀ i, v i ∈ P)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (C : Fin m → (Fin d → ℝ) →ₗ[ℝ] ℝ) (b : Fin m → ℝ)
    (hx : (∑ i, w i • v i) ∈
      (P ∩ {y | ∀ j, C j y ≤ b j}).extremePoints ℝ) :
    (∀ t : Fin n → ℝ, (∑ i, t i) = 0 →
      (∀ j, C j (∑ i, w i • v i) = b j → C j (∑ i, t i • v i) = 0) →
      (∑ i, t i • v i) = 0) ∧
    (LinearIndependent ℝ (fun i => ((1 : ℝ), v i)) →
      let A := {j : Fin m // C j (∑ i, w i • v i) = b j}
      LinearIndependent ℝ (fun i => ((1 : ℝ), fun j : A => C j.val (v i))) ∧
        n ≤ Nat.card A + 1) := by sorry
