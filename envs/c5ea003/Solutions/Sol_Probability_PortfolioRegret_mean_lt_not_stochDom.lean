-- Prove2me | solution 1 for Probability.PortfolioRegret.mean_lt_not_stochDom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:35.41923+00:00
-- url     : https://prove2.me/submissions/caf57d3e-3461-4aa7-ae40-7cbe71fbd010

-- Sol generated from Probability/PortfolioRegretTail.lean
import Mathlib
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
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











/-! ## Layer cake and stochastic dominance -/







open Probability.PortfolioRegret in
theorem solution:
    ∃ (w : Fin 2 → ℚ) (X Y : Fin 2 → ℕ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i * (X i : ℚ)) < (∑ i, w i * (Y i : ℚ)) ∧
      ¬ StochDom w X Y := by
  classical
  refine ⟨![1/2, 1/2], ![0, 10], ![6, 6], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · simp [Fin.sum_univ_two]; norm_num
  · intro h
    have h6 := h 6
    have hX : PrGT ![1/2, 1/2] ![0, 10] 6 = 1/2 := by
      have : (univ.filter (fun i : Fin 2 => 6 < (![0, 10] : Fin 2 → ℕ) i)) = {1} := by
        ext i; fin_cases i <;> simp
      simp [PrGT, Pr, this]
    have hY : PrGT ![1/2, 1/2] ![6, 6] 6 = 0 := by
      have : (univ.filter (fun i : Fin 2 => 6 < (![6, 6] : Fin 2 → ℕ) i)) = ∅ := by
        ext i; fin_cases i <;> simp
      simp [PrGT, Pr, this]
    rw [hX, hY] at h6
    linarith
