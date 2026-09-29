-- Prove2me | solution 1 for Probability.PortfolioRegret.share_realizability
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:38.336013+00:00
-- url     : https://prove2.me/submissions/fa2af4d8-dbff-423a-b6c9-e539ccaeb6e3

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


theorem oracle_diagCost {P : ℚ} (hP : 1 ≤ P) (ω : S) : oracleCost (diagCost P) ω = 1 := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ ?_)
  · have h : diagCost P ω ω = 1 := by simp [diagCost]
    exact h ▸ Finset.inf'_le _ (mem_univ ω)
  · intro s _
    by_cases h : s = ω
    · simp [diagCost, h]
    · simpa [diagCost, h] using hP

/-- Each member of the canonical portfolio wins exactly on its own class. -/
theorem winner_set_diagCost {P : ℚ} (hP : 1 < P) (s : S) :
    (univ.filter (fun ω : S => diagCost P ω s = oracleCost (diagCost P) ω)) = {s} := by
  ext ω
  simp only [mem_filter, mem_univ, true_and, mem_singleton, oracle_diagCost hP.le, diagCost]
  constructor
  · intro h
    by_cases hs : s = ω
    · exact hs.symm
    · rw [if_neg hs] at h; exact absurd h (by intro hh; exact absurd hh.symm hP.ne)
  · intro h; rw [if_pos h.symm]


/-! ## The tail must carry the regret -/





open Probability.PortfolioRegret in
theorem solution(p : S → ℚ) (P : ℚ) (hP : 1 < P) :
    (∀ s : S, ∑ ω ∈ univ.filter (fun ω : S => diagCost P ω s = oracleCost (diagCost P) ω),
        p ω = p s) ∧
    (∀ s : S, EV p (fun ω => diagCost P ω s) = p s + (∑ ω, p ω - p s) * P) ∧
    (∀ s t : S, p t ≤ p s → EV p (fun ω => diagCost P ω s) ≤ EV p (fun ω => diagCost P ω t)) := by
  have hev : ∀ s : S, EV p (fun ω => diagCost P ω s) = p s + (∑ ω, p ω - p s) * P := by
    intro s
    have hpt : ∀ ω : S, p ω * diagCost P ω s
        = p ω * P + (if ω = s then p ω * (1 - P) else 0) := by
      intro ω
      by_cases h : ω = s
      · subst h; simp [diagCost]; ring
      · simp [diagCost, h, Ne.symm h]
    rw [EV, Finset.sum_congr rfl (fun ω _ => hpt ω), Finset.sum_add_distrib,
      Finset.sum_ite_eq' univ s (fun ω => p ω * (1 - P)), ← Finset.sum_mul]
    simp
    ring
  refine ⟨fun s => by rw [winner_set_diagCost hP s, Finset.sum_singleton], hev, ?_⟩
  intro s t hts
  rw [hev s, hev t]
  nlinarith [hP, hts]
