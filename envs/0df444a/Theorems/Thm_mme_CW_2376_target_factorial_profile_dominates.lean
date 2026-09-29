-- Prove2me | Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates
-- name    : mme_CW_2376_target_factorial_profile_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:11:34.791853+00:00
-- url     : https://prove2.me/theorems/e3aa26ed-6ef1-4acf-ac81-e1341053e323
-- title:
--   The optimized CW joint profile maximizes its multinomial term
-- statement:
--   Let $beta$ be the optimized equation-(13) multiplicity table on the fifteen supported joint types of the squared Coppersmith--Winograd tensor, at a positive scale $m$. Let $a$ be any other nonnegative integral table on those types. Assume that $a$ and $beta$ have the same total mass and the same five grade marginals in each of the three tensor modes. Then the product of the factorials of the target multiplicities is at most the corresponding product for $a$.
--
--   Equivalently, when the multinomial numerator is fixed, the optimized CW profile has at least as large a multinomial coefficient as every competing supported profile with the same marginals. This is the exact finite profile-dominance step required before applying the Salem--Spencer hash to the full marginal-supported hypergraph.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), dominant-profile argument surrounding equation (13) on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_CW_2376_target_product_weight_identity

open MME BigOperators

theorem mme_CW_2376_target_factorial_profile_dominates
    (m : ℕ) (hm : 0 < m) (a : (Fin 3 → Fin 5) → ℕ)
    (ha : ∀ i : Fin 3, ∀ r : Fin 5,
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma i = r then a sigma else 0) =
      ∑ sigma ∈ cw2376TargetJointTypes,
        if sigma i = r then cw2376ProfileMultiplicity m sigma else 0)
    (htotal : (∑ sigma ∈ cw2376TargetJointTypes, a sigma) =
      ∑ sigma ∈ cw2376TargetJointTypes,
        cw2376ProfileMultiplicity m sigma) :
    (∏ sigma ∈ cw2376TargetJointTypes,
        (cw2376ProfileMultiplicity m sigma).factorial) ≤
      ∏ sigma ∈ cw2376TargetJointTypes, (a sigma).factorial := by
  sorry
