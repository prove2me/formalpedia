-- Prove2me | Theorems.Thm_Hirsch_triangular_extreme_points_force_exponential_affine_levels
-- name    : Hirsch.triangular_extreme_points_force_exponential_affine_levels
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-16T21:55:30.720691+00:00
-- url     : https://prove2.me/theorems/75f43150-aee7-4659-a310-709b352b68a7
-- title:
--   Construct triangular extreme points with exponential affine coordinate-level obstruction
-- statement:
--   For every real 0<e<1/2 and every n>=0, construct a finite set V of exactly 2^(n+1) extreme points of the explicit triangular H-polytope in R^(n+1): every coordinate is between zero and one, and e*y_j<=y_i<=1-e*y_j whenever j=i+1. This is the classical Klee-Minty box with coordinate order reversed. For EVERY injective real linear map T to R^r and every translation, some output coordinate takes K distinct values on this ACTUAL V with 2^(n+1)<=K(K-1). The point family, extremality, exponential cardinality, positive distinct parallel displacements and detecting coordinate are conclusions, not assumed inputs. The proof constructs binary recursive points, proves interval separation and injectivity, proves extremality against arbitrary feasible open-segment endpoints, and reuses the already accepted finite parallel-displacement counting theorem. It does not assert a large graph diameter, a shortest-path theorem, a characterization of every extreme point, or a lower bound for general projected extensions. No unrestricted Polynomial Hirsch proof is claimed.
-- source:
--   Constructive formal bridge for research/AFFINE_LEVEL_BARRIER.md and research/PARALLEL_AFFINE_LEVELS_HANDOFF.md in jjoshua2/prove2me-work at129c7d4947113733fca17b9b600e93ac65470b12. Reuses the accepted proof body from theorem7ccd31e6-1b96-4c43-b1c4-f8c180eec7b8 (#279), with only its root name changed. Classical triangular family: Gaertner, Helbling, Ota and Takahashi, Large Shadows from Sparse Inequalities, arXiv:1308.2495v1 Section4. No historical-priority claim.

import Mathlib
set_option autoImplicit false

theorem Hirsch.triangular_extreme_points_force_exponential_affine_levels (e : ℝ) (he : 0 < e) (he2 : e < 1/2) (n : ℕ) :
    ∃ V : Finset (Fin (n+1) → ℝ), V.card = 2^(n+1) ∧
      (∀ x ∈ V, x ∈
        ({y : Fin (n+1) → ℝ |
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧
          ∀ (i j : Fin (n+1)), i.val+1 = j.val → e*y j ≤ y i ∧ y i ≤ 1-e*y j}).extremePoints ℝ) ∧
      ∀ (r : ℕ) (T : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin r → ℝ)),
        Function.Injective T → ∀ offset : Fin r → ℝ,
          ∃ j : Fin r, 2^(n+1) ≤
            (V.image (fun x => (T x) j + offset j)).card *
              ((V.image (fun x => (T x) j + offset j)).card - 1) := by sorry
