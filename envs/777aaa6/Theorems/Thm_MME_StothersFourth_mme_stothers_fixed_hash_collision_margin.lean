-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_hash_collision_margin
-- name    : MME.StothersFourth.mme_stothers_fixed_hash_collision_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:17:27.505295+00:00
-- url     : https://prove2.me/theorems/07b0f083-5e4b-4497-b1c4-8d6ec5a47e51
-- title:
--   Fixed Stothers polynomial loss fits the Behrend collision margin
-- statement:
--   Put D = (6(N+1))^100 D*. If the chosen prime satisfies p ≤ D exp(2000 √(1000N+1)) and the progression-free set has at least 6D elements, then the prime-loss term and the three collision-mode budgets fit inside D*|S|: p^2 exp(-10^6 √(N+1)) + 3D*D ≤ D*|S|.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equations (3.3)--(3.4), https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The constants are an explicit slackened polynomial-versus-exponential specialization for the fixed fourth-power profile.

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_mme_stothers_fixed_outer_profile

open MME BigOperators Filter Topology

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_hash_collision_margin
    (N Dstar p Scard : ℕ)
    (hpScaled :
      (p : ℝ) ≤
        ((((6 * (N + 1)) ^ 100 * Dstar : ℕ) : ℝ)) *
          Real.exp
            (2000 *
              Real.sqrt ((((1000 * N + 1 : ℕ) : ℝ)))))
    (hSsix :
      (6 * (((6 * (N + 1)) ^ 100 * Dstar) : ℕ) : ℝ) ≤
        (Scard : ℝ)) :
    let D : ℕ := (6 * (N + 1)) ^ 100 * Dstar
    (p : ℝ) ^ 2 *
          Real.exp
            (-1000000 * Real.sqrt ((((N + 1 : ℕ) : ℝ)))) +
        3 * (Dstar : ℝ) * (D : ℝ) ≤
      (Dstar : ℝ) * (Scard : ℝ) := by
  sorry
