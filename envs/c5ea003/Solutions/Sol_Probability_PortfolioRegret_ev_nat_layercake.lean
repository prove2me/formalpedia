-- Prove2me | solution 1 for Probability.PortfolioRegret.ev_nat_layercake
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:49:46.347104+00:00
-- url     : https://prove2.me/submissions/7376259f-bb7d-4cb1-aff6-72a255eebf55

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
theorem solution[Fintype Ω] (w : Ω → ℚ) (X : Ω → ℕ) (B : ℕ) (hB : ∀ ω, X ω ≤ B) :
    ∑ ω, w ω * (X ω : ℚ) = ∑ t ∈ range B, PrGT w X t := by
  classical
  have hstep : ∀ t : ℕ, PrGT w X t = ∑ ω, if t < X ω then w ω else 0 := by
    intro t; simp [PrGT, Pr, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun t _ => hstep t), Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hset : (range B).filter (fun t => t < X ω) = range (X ω) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le h (hB ω), h⟩
  rw [← Finset.sum_filter, hset, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
