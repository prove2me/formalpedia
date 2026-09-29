-- Prove2me | Theorems.Thm_smale_17_points_problem
-- name    : smale_17_points_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T20:42:09.019812+00:00
-- url     : https://prove2.me/theorems/a4e50ab7-5efc-4747-9887-15964503994d
-- statement:
--   Smale's 17th problem (1998): Can the eigenvalues of a symmetric matrix be computed with polynomial cost (in the BSS model over ℝ)? More generally, Smale's 7th problem asks for efficient algorithms for systems of polynomial equations over ℝ. Open for many formulations.
-- source:
--   https://en.wikipedia.org/wiki/Smale%27s_problems

import Mathlib

import Mathlib

theorem smale_17_points_problem :
    ∃ (algo : (ℕ → ℕ → ℝ) → ℕ → Option (ℕ → ℝ)),
      ∀ (n : ℕ) (coeffs : ℕ → ℕ → ℝ),
        (∃ x : ℕ → ℝ, ∀ i < n, ∑ j ∈ Finset.range n, coeffs i j * x j = 0) →
        ∃ T : ℕ, (algo coeffs T).isSome ∧
          ∀ sol, algo coeffs T = some sol →
            ∀ i < n, ∑ j ∈ Finset.range n, coeffs i j * sol j = 0 := by
  sorry
