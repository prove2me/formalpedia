-- Prove2me | Theorems.Thm_mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
-- name    : mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:02:03.342281+00:00
-- url     : https://prove2.me/theorems/6d3eb4a8-14cc-4921-bf33-371e45c70d71
-- title:
--   Seven-eighths mass pays the weighted first-hash collision budget
-- statement:
--   Assume an aggregate retained mass of at least seven eighths of the full affine incidence mass. If the common prime satisfies 8d≤p and the weighted X/Y collision cost is bounded by the usual directed degree estimate, then the mass pays both the target average-state term at scale cap·|T|·|S|/(2p²) and the entire collision cost. This is the numerical 1/2+1/4≤7/8 step in the common-state DWZ selection.
-- source:
--   Duan--Wu--Zhou, aggregate Claim 6.8 mass combined with the first-hash collision budget.

import Mathlib

set_option autoImplicit false

/-- Numerical core of the correlated DWZ source selection.  A `7/8` total
nonhole-mass estimate and the usual first-hash collision estimate leave the
original `1/2` retained mass whenever `8d ≤ p`. -/

theorem mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
    (N p target bucket degree cap : ℕ)
    (hp : 0 < p) (hmod : 8 * degree ≤ p)
    (massTotal collisionCost : ℝ)
    (hmass :
      (7 / 8 : ℝ) *
          ((cap : ℝ) * (target : ℝ) * (bucket : ℝ) *
            (p : ℝ) ^ (N + 1)) ≤ massTotal)
    (hcollision : collisionCost ≤
      (cap : ℝ) * (2 * (target : ℝ) * (degree : ℝ)) *
        (bucket : ℝ) * (p : ℝ) ^ N) :
    (p : ℝ) ^ (N + 3) *
          (((cap : ℝ) * (target : ℝ) * (bucket : ℝ)) /
            (2 * (p : ℝ) ^ 2)) +
        collisionCost ≤ massTotal := by
  sorry
