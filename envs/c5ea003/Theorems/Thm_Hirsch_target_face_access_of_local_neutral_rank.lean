-- Prove2me | Theorems.Thm_Hirsch_target_face_access_of_local_neutral_rank
-- name    : Hirsch.target_face_access_of_local_neutral_rank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T18:21:16.837186+00:00
-- url     : https://prove2.me/theorems/4da3a606-c8d4-4570-a246-afbff569cc7a
-- title:
--   Target supporting-face access controlled by local active neutral rank
-- statement:
--   Let P be a nonempty bounded H-polytope described by n inequalities in R^d, and u,v distinct extreme points. Assume that at every extreme point x avoiding all nonzero supporting rows tight at v, the nonzero row normals active at x but active at neither u nor v belong to a linear subspace K_x of dimension at most r. K_x may vary with x. Then some extreme point z on some nonzero supporting row tight at v can be reached from u by a padded edge walk of length n*2^(max(r-3,0))+1. No separation assumption is required: a source already on a target row is handled by a constant walk. In particular r<=3 gives n+1 steps; r bounded logarithmically in n gives a polynomial estimate. This is not a uniform polynomial Hirsch bound, not access to an arbitrarily prescribed row, and not a walk to v. The number n counts describing rows, not necessarily irredundant facets. The accepted parallel-neutral two-edge theorem is sharper at rank one; this result extends the method to local subspaces of arbitrary finite rank.
-- source:
--   Working derivation for the Polynomial Hirsch mission, 2026-09-06, jjoshua2/prove2me-work branch chatgpt/local-neutral-rank. Uses the public proved Hirsch.larman_bound. No literature priority claim.

import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch

theorem Hirsch.target_face_access_of_local_neutral_rank
    (d n r : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
          ⟪a i, x⟫ = b i → a i ∈ K) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (n * 2 ^ (r - 3) + 1) = z ∧
        ∀ j < n * 2 ^ (r - 3) + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry
