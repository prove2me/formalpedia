-- Prove2me | solution 1 for Probability.PortfolioRegret.mean_elimination_unsafe
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:34.86943+00:00
-- url     : https://prove2.me/submissions/ac5c5ea8-b620-4580-a68a-bf286c5fd2b3

-- Sol generated from Probability/PortfolioElimination.lean
import Mathlib
import Definitions.Def_Probability_PortfolioElimination
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
import Theorems.Thm_Probability_PortfolioRegret_oracleCost_fin_two
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Eliminating a portfolio member: what is safe and what is not

Fourth cycle of the portfolio programme, formalising the ledger requirement that
*eliminations need dominance arguments, not mean comparisons*.

* `oracleOn` — the oracle restricted to a sub-portfolio.
* `oracleOn_erase_of_dominates` / `ev_oracleOn_erase_of_dominates` — **safe
  elimination**: a member that is dominated *pointwise* by another member may be
  deleted without changing the oracle, instancewise and in expectation.
* `mean_elimination_unsafe` — **unsafe elimination**: a member whose mean cost is
  twice that of another can nevertheless be the only member that keeps the oracle
  cheap; deleting it doubles the oracle's expected cost.  A mean comparison is
  therefore never sufficient grounds for elimination.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}





theorem oracleCost_elimCost (ω : Fin 2) : oracleCost elimCost ω = 1 := by
  fin_cases ω
  · rw [oracleCost_fin_two]
    show min (1 : ℚ) 5 = 1
    norm_num
  · rw [oracleCost_fin_two]
    show min (5 : ℚ) 1 = 1
    norm_num



open Probability.PortfolioRegret in
theorem solution:
    (∀ i, 0 ≤ tailW i) ∧ (∑ i, tailW i = 1) ∧
    EV tailW (fun ω => elimCost ω 0) = 2 ∧
    EV tailW (fun ω => elimCost ω 1) = 4 ∧
    EV tailW (oracleCost elimCost) = 1 ∧
    EV tailW (oracleOn ((univ : Finset (Fin 2)).erase 1) ⟨0, by decide⟩ elimCost) = 2 := by
  refine ⟨fun i => by fin_cases i <;> norm_num [tailW], by norm_num [tailW, Fin.sum_univ_two],
    ?_, ?_, ?_, ?_⟩
  · norm_num [EV, tailW, elimCost, Fin.sum_univ_two]
  · norm_num [EV, tailW, elimCost, Fin.sum_univ_two]
  · simp only [EV, oracleCost_elimCost, mul_one]
    norm_num [tailW, Fin.sum_univ_two]
  · have hsingle : ((univ : Finset (Fin 2)).erase 1) = {0} := by decide
    have hval : oracleOn ((univ : Finset (Fin 2)).erase 1) ⟨0, by decide⟩ elimCost
        = fun ω => elimCost ω 0 :=
      funext fun ω => by rw [oracleOn]; simp [hsingle]
    rw [hval]
    norm_num [EV, tailW, elimCost, Fin.sum_univ_two]
