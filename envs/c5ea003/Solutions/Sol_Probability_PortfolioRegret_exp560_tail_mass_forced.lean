-- Prove2me | solution 1 for Probability.PortfolioRegret.exp560_tail_mass_forced
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:56:04.959555+00:00
-- url     : https://prove2.me/submissions/1c32e4c3-3891-4fd9-8df6-edf635f7d925

-- Sol generated from Probability/PortfolioShareRealizability.lean
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
import Definitions.Def_Probability_PortfolioShareRealizability
import Theorems.Thm_Probability_PortfolioRegret_exp560W_nonneg
import Theorems.Thm_Probability_PortfolioRegret_exp560W_sum
import Theorems.Thm_Probability_PortfolioRegret_exp560_ev_const
import Theorems.Thm_Probability_PortfolioRegret_tail_mass_lower_bound
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


/-- The tail mass is bounded below by the excess of the mean over the threshold,
normalised by the range: a large mean regret *forces* a tail. -/
theorem tail_mass_ge_of_ev {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w X : Ω → ℚ)
    (hw0 : ∀ ω, 0 ≤ w ω) (hw : ∑ ω, w ω = 1) (t K : ℚ) (ht : t < K) (hub : ∀ ω, X ω ≤ K) :
    (EV w X - t) / (K - t) ≤ Pr w (fun ω => t < X ω) := by
  have h := tail_mass_lower_bound w X hw0 hw t K hub
  rw [div_le_iff₀ (by linarith : (0:ℚ) < K - t)]
  linarith [h]



open Probability.PortfolioRegret in
theorem solution:
    (42 : ℚ) / 100 ≤ Pr exp560W (fun x => 1 < exp560Cost x 0) := by
  have hub : ∀ x : Fin 5 × Fin 2, exp560Cost x 0 ≤ penalty := by
    intro x
    by_cases h : (0 : Fin 5) = x.1
    · simp [exp560Cost, h, penalty]
      norm_num
    · simp [exp560Cost, h]
  have hmean : EV exp560W (fun x => exp560Cost x 0) = 4117/1000 := by
    rw [exp560_ev_const 0]
    norm_num [exp560Mean, classW, penalty]
  have h := tail_mass_ge_of_ev exp560W (fun x => exp560Cost x 0) exp560W_nonneg exp560W_sum
    1 penalty (by norm_num [penalty]) hub
  rw [hmean] at h
  refine le_trans (le_of_eq ?_) h
  norm_num [penalty]
