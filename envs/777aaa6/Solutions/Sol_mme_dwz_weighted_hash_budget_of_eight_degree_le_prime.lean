-- Prove2me | solution 1 for mme_dwz_weighted_hash_budget_of_eight_degree_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T22:03:19.94585+00:00
-- url     : https://prove2.me/submissions/14f6585a-80c3-430f-af7f-532db50ff998

import Mathlib

set_option autoImplicit false
set_option warningAsError true

/-- Numerical core of the correlated DWZ source selection.  A `7/8` total
nonhole-mass estimate and the usual first-hash collision estimate leave the
original `1/2` retained mass whenever `8d ≤ p`. -/
theorem solution
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
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmodR : (8 : ℝ) * (degree : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hmod
  let U : ℝ :=
    (cap : ℝ) * (target : ℝ) * (bucket : ℝ) * (p : ℝ) ^ N
  have hU : 0 ≤ U := by
    dsimp only [U]
    positivity
  have hdegreeQuarter : 2 * (degree : ℝ) * U ≤
      (1 / 4 : ℝ) * (p : ℝ) * U := by
    have hscaled := mul_le_mul_of_nonneg_right hmodR hU
    nlinarith
  have hcollision' : collisionCost ≤
      (1 / 4 : ℝ) *
        ((cap : ℝ) * (target : ℝ) * (bucket : ℝ) *
          (p : ℝ) ^ (N + 1)) := by
    calc
      collisionCost ≤
          (cap : ℝ) * (2 * (target : ℝ) * (degree : ℝ)) *
            (bucket : ℝ) * (p : ℝ) ^ N := hcollision
      _ = 2 * (degree : ℝ) * U := by
        dsimp only [U]
        ring
      _ ≤ (1 / 4 : ℝ) * (p : ℝ) * U := hdegreeQuarter
      _ = (1 / 4 : ℝ) *
          ((cap : ℝ) * (target : ℝ) * (bucket : ℝ) *
            (p : ℝ) ^ (N + 1)) := by
        dsimp only [U]
        rw [pow_succ]
        ring
  have hstateTerm :
      (p : ℝ) ^ (N + 3) *
          (((cap : ℝ) * (target : ℝ) * (bucket : ℝ)) /
            (2 * (p : ℝ) ^ 2)) =
        (1 / 2 : ℝ) *
          ((cap : ℝ) * (target : ℝ) * (bucket : ℝ) *
            (p : ℝ) ^ (N + 1)) := by
    rw [show N + 3 = (N + 1) + 2 by omega, pow_add]
    field_simp
  have htotalNonneg : 0 ≤
      (cap : ℝ) * (target : ℝ) * (bucket : ℝ) *
        (p : ℝ) ^ (N + 1) := by positivity
  rw [hstateTerm]
  norm_num at hmass hcollision' ⊢
  linarith

