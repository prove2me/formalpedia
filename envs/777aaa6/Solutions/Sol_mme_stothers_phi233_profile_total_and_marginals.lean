-- Prove2me | solution 1 for mme_stothers_phi233_profile_total_and_marginals
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:36:56.320106+00:00
-- url     : https://prove2.me/submissions/3ad570a1-eb76-4868-877c-7fd3f789c898

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N) :
    (∑ r : Fin 10,
        MME.StothersFourth.Phi233.profileMultiplicity
          alpha beta gamma delta r) = 2 * N ∧
      ∀ i : Fin 3, ∀ k : Fin 5,
        (∑ r : Fin 10,
          if MME.StothersFourth.Phi233.pattern r i = k then
            MME.StothersFourth.Phi233.profileMultiplicity
              alpha beta gamma delta r
          else 0) =
        MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta i k := by
  constructor
  · simp [MME.StothersFourth.Phi233.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  · intro i k
    fin_cases i <;> fin_cases k <;>
      simp [MME.StothersFourth.Phi233.pattern,
        MME.StothersFourth.Phi233.profileMultiplicity,
        MME.StothersFourth.Phi233.marginalMultiplicity,
        MME.cwSquareBlockType, Fin.sum_univ_succ] <;> omega
