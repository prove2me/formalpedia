-- Prove2me | Theorems.Thm_mme_CW_2376_compatible_profile_completion_sum_le
-- name    : mme_CW_2376_compatible_profile_completion_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:15:44.142442+00:00
-- url     : https://prove2.me/theorems/562def78-77b2-4f62-9a28-7c2eefda9a5c
-- title:
--   Compatible CW completion profiles cost only their count times the target term
-- statement:
--   Fix a positive CW scale $m$ and a finite family $T$ of supported joint multiplicity tables, each with the optimized profile's three marginals and total mass. Let $A$ be any fixed natural-number numerator. For each table, divide $A$ by the product of its fifteen cell factorials. The sum of these completion terms is at most the number of tables in $T$ times the corresponding target-profile term.
--
--   In the outer laser count, $A$ is the product of the five fixed marginal factorials. The theorem converts exact target multinomial dominance into a bound for the full compatible completion degree, while retaining every supported joint profile.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) and the compatible-profile count on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates

open MME BigOperators

theorem mme_CW_2376_compatible_profile_completion_sum_le
    (m : ℕ) (hm : 0 < m)
    (T : Finset ((Fin 3 → Fin 5) → ℕ)) (numerator : ℕ)
    (hT : ∀ a ∈ T,
      (∀ i : Fin 3, ∀ r : Fin 5,
        (∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then a sigma else 0) =
        ∑ sigma ∈ cw2376TargetJointTypes,
          if sigma i = r then cw2376ProfileMultiplicity m sigma else 0) ∧
      (∑ sigma ∈ cw2376TargetJointTypes, a sigma) =
        ∑ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma) :
    (∑ a ∈ T, numerator /
        ∏ sigma ∈ cw2376TargetJointTypes, (a sigma).factorial) ≤
      T.card * (numerator /
        ∏ sigma ∈ cw2376TargetJointTypes,
          (cw2376ProfileMultiplicity m sigma).factorial) := by
  sorry
