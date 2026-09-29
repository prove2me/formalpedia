-- Prove2me | solution 1 for Probability.PortfolioRegret.median_one_mean_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:35.985747+00:00
-- url     : https://prove2.me/submissions/cc52145e-ecb0-42c0-9d3c-4049913639b0

-- Sol generated from Probability/PortfolioRegretTail.lean
import Mathlib
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
import Theorems.Thm_Probability_PortfolioRegret_oracleCost_fin_two
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The regret tail: median blindness and the failure of mean-based elimination

Companion to `Probability.PortfolioRegretCore`.  Two phenomena observed in
experiment 560 are isolated and proved here.

* **Median blindness.**  Every scheduling strategy in the experiment had median
  regret ratio exactly `1.000`, while the *mean* regret was large: the loss lives
  entirely in a thin tail.  `median_one_mean_unbounded` shows this is not an
  artifact — for every prescribed level `M` there is a portfolio whose *optimal
  static* strategy has median regret ratio `1` and mean regret ratio `> M`.
  Hence the median is a provably uninformative statistic for portfolio
  selection.

* **Failure of mean-based elimination (the "H3" ledger entry).**  Eliminating a
  portfolio member because its *mean* cost is larger is not a
  dominance-in-distribution argument.  `ev_le_of_stochDom` proves the valid
  direction (stochastic dominance implies a mean inequality, via an exact finite
  layer-cake identity `ev_nat_layercake`), while `mean_lt_not_stochDom` exhibits
  a variance-tail counterexample to the converse.
-/

open Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}

/-! ## Probabilities, ratios and medians -/







theorem oracleCost_tailCost {M : ℚ} (hM : 0 ≤ M) (ω : Fin 2) : oracleCost (tailCost M) ω = 1 := by
  fin_cases ω
  · rw [oracleCost_fin_two]
    show min (1 : ℚ) (8 * M + 8) = 1
    exact min_eq_left (by linarith)
  · rw [oracleCost_fin_two]
    show min (4 * M + 4) (1 : ℚ) = 1
    exact min_eq_right (by linarith)

theorem ev_tailCost_zero (M : ℚ) : EV tailW (fun ω => tailCost M ω 0) = M + 7/4 := by
  simp [EV, tailW, tailCost, Fin.sum_univ_two]
  ring

theorem ev_tailCost_one (M : ℚ) : EV tailW (fun ω => tailCost M ω 1) = 6 * M + 25/4 := by
  simp [EV, tailW, tailCost, Fin.sum_univ_two]
  ring


/-! ## Layer cake and stochastic dominance -/







open Probability.PortfolioRegret in
theorem solution(M : ℚ) (hM : 0 ≤ M) :
    (∀ ω, 0 ≤ tailW ω) ∧ (∑ ω, tailW ω = 1) ∧
    (∀ ω, 0 < oracleCost (tailCost M) ω) ∧
    bestConstant tailW (tailCost M) = EV tailW (fun ω => tailCost M ω 0) ∧
    1 / 2 ≤ Pr tailW (fun ω => tailCost M ω 0 = oracleCost (tailCost M) ω) ∧
    M < EV tailW (regretRatio (tailCost M) 0) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; fin_cases ω <;> norm_num [tailW]
  · norm_num [tailW, Fin.sum_univ_two]
  · intro ω; rw [oracleCost_tailCost hM]; norm_num
  · -- the best constant strategy is strategy `0`
    refine le_antisymm (Finset.inf'_le _ (mem_univ 0)) (Finset.le_inf' _ _ ?_)
    intro i _
    fin_cases i
    · exact le_of_eq rfl
    · show EV tailW (fun ω => tailCost M ω 0) ≤ EV tailW (fun ω => tailCost M ω 1)
      rw [ev_tailCost_zero, ev_tailCost_one]; linarith
  · -- the median regret ratio is `1`: strategy `0` ties the oracle on mass `3/4`
    have hfil : (univ.filter
        (fun ω : Fin 2 => tailCost M ω 0 = oracleCost (tailCost M) ω)) = {0} := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        oracleCost_tailCost hM]
      fin_cases ω
      · show tailCost M 0 0 = 1 ↔ (0 : Fin 2) = 0
        simp [tailCost]
      · show tailCost M 1 0 = 1 ↔ (1 : Fin 2) = 0
        rw [show tailCost M 1 0 = 4 * M + 4 from rfl]
        constructor
        · intro h; exfalso; linarith
        · intro h; exact absurd h (by decide)
    rw [Pr, hfil]
    norm_num [tailW]
  · -- but the mean regret ratio is `M + 7/4`
    have heq : EV tailW (regretRatio (tailCost M) 0) = M + 7/4 := by
      have hr : regretRatio (tailCost M) 0 = fun ω => tailCost M ω 0 :=
        funext fun ω => by rw [regretRatio, oracleCost_tailCost hM, div_one]
      rw [hr]
      exact ev_tailCost_zero M
    rw [heq]; linarith
