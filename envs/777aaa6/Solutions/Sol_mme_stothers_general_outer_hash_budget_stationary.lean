-- Prove2me | solution 1 for mme_stothers_general_outer_hash_budget_stationary
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T05:00:49.120436+00:00
-- url     : https://prove2.me/submissions/f2dad351-9837-45b1-b2bd-d7384753c753

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.NatCast
import Theorems.Thm_mme_stothers_general_bounded_degree_data
import Theorems.Thm_mme_stothers_general_outer_hash_budget_of_bounded_degree_data
import Theorems.Thm_mme_stothers_general_hash_conditional_entropy_of_stationary

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (base bstar : Fin 10 → ℕ)
    (hbase : ∀ r, 0 < base r) (hbstar : ∀ r, 0 < bstar r)
    (hsame : ∀ j, MME.StothersFourth.genMarginalBaseCount bstar j =
      MME.StothersFourth.genMarginalBaseCount base j)
    (hInN : MME.StothersFourth.InN (MME.StothersFourth.genProfileB bstar)) :
    ∀ᶠ m : ℕ in atTop,
      let N := MME.StothersFourth.genOuterLength base m
      let V : ℝ :=
        (N.factorial : ℝ) /
          ∏ j : Fin 9, ((MME.StothersFourth.genMarginalCount base m j).factorial : ℝ)
      ∃ E : Finset (MME.StothersFourth.GenMarginalSupportedAddress base m),
        MME.StothersFourth.GenMarginalVertexClosed E ∧
        ((MME.StothersFourth.genTargetAmbientCollisions E).card : ℝ) +
            V * ((MME.StothersFourth.genHashTargetStarDegree base m : ℝ) /
                  (((6 * (N + 1)) ^ 100 *
                    MME.StothersFourth.genHashTargetStarDegree bstar m : ℕ) : ℝ)) *
              Real.exp
                (-1000000 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
          ((MME.StothersFourth.genExactTargetEdges E).card : ℝ) := by
  exact mme_stothers_general_outer_hash_budget_of_bounded_degree_data base hbase
    (fun m ↦ MME.StothersFourth.genHashTargetStarDegree base m)
    (fun m ↦ (6 * (MME.StothersFourth.genOuterLength base m + 1)) ^ 100 *
      MME.StothersFourth.genHashTargetStarDegree bstar m)
    (mme_stothers_general_bounded_degree_data base bstar hbase hbstar hsame
      (mme_stothers_general_hash_conditional_entropy_of_stationary base bstar
        hbase hbstar hsame hInN))
