-- Prove2me | solution 1 for Probability.PortfolioRegret.tail_mass_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:49.356085+00:00
-- url     : https://prove2.me/submissions/acadd6e7-c611-42e0-992c-1481733cd503

-- Sol generated from Probability/PortfolioShareRealizability.lean
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
import Definitions.Def_Probability_PortfolioShareRealizability
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Winner shares measure the sampler, and the regret really does live in the tail

Third cycle of the portfolio programme.  Two ledger entries of experiment 560
are turned into theorems.

**Sampler dependence.**  The measured oracle winner shares
`(0.580, 0.345, 0.045, 0.028, 0.002)` are often read as a statement about the
algorithms.  `share_realizability` shows that they are a statement about the
*instance sampler*: for **every** prescribed share vector `p` there is a sampler
on which the oracle winner shares are exactly `p`, and on which the static
ranking of the portfolio is exactly the ranking of `p`.  Consequently "no
universal winner" cannot be inferred from — nor refuted by — any single sampler,
which is precisely the scope caveat recorded in the ledger.

**The tail carries the regret.**  `tail_mass_lower_bound` and
`tail_mass_ge_of_ev` prove a Markov-type reverse bound: if a cost is at most `K`
and its mean is `R`, then the event `{cost > t}` must carry mass at least
`(R - t) / (K - t)`.  Applied to the exp-560 portfolio it shows that the
`0.42`-mass minority on which `ρ` loses is *forced* by the measured mean regret
`3.117`; the fat tail cannot be an artifact of a few outliers.
-/

open Probability.PortfolioRegret

open Finset

/-! ## Sampler dependence of the winner shares -/

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]





/-! ## The tail must carry the regret -/





open Probability.PortfolioRegret in
theorem solution{Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w X : Ω → ℚ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (t K : ℚ) (hub : ∀ ω, X ω ≤ K) :
    EV w X ≤ t + (K - t) * Pr w (fun ω => t < X ω) := by
  classical
  set A : Finset Ω := univ.filter (fun ω => t < X ω) with hA
  have hsplit : ∑ ω ∈ A, w ω * X ω + ∑ ω ∈ univ.filter (fun ω => ¬ t < X ω), w ω * X ω
      = ∑ ω, w ω * X ω := Finset.sum_filter_add_sum_filter_not univ _ _
  have hbulkmass : ∑ ω ∈ univ.filter (fun ω => ¬ t < X ω), w ω = 1 - Pr w (fun ω => t < X ω) := by
    have := Finset.sum_filter_add_sum_filter_not univ (fun ω => t < X ω) w
    rw [Pr, hA] at *
    linarith [this, hw]
  have htail : ∑ ω ∈ A, w ω * X ω ≤ K * Pr w (fun ω => t < X ω) := by
    rw [Pr, ← hA, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by
      rw [mul_comm K (w ω)]
      exact mul_le_mul_of_nonneg_left (hub ω) (hw0 ω)
  have hbulk : ∑ ω ∈ univ.filter (fun ω => ¬ t < X ω), w ω * X ω
      ≤ t * (1 - Pr w (fun ω => t < X ω)) := by
    rw [← hbulkmass, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    have hx : X ω ≤ t := not_lt.mp (Finset.mem_filter.mp hω).2
    rw [mul_comm t (w ω)]
    exact mul_le_mul_of_nonneg_left hx (hw0 ω)
  have : EV w X ≤ K * Pr w (fun ω => t < X ω) + t * (1 - Pr w (fun ω => t < X ω)) := by
    rw [EV, ← hsplit]; linarith
  linarith [this]
