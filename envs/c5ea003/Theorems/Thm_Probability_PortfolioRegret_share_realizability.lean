-- Prove2me | Theorems.Thm_Probability_PortfolioRegret_share_realizability
-- name    : Probability.PortfolioRegret.share_realizability
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:59:35.528012+00:00
-- url     : https://prove2.me/theorems/5d29db8a-3cca-4b5a-af8a-8f93fa108c5e
-- title:
--   Winner shares are a property of the sampler.
-- statement:
--   **Winner shares are a property of the sampler.**  For every probability
--   vector `p` on the portfolio there is a sampler realising `p` as the vector of
--   oracle winner shares, and on that sampler the expected cost of a member is a
--   strictly decreasing function of its share: the static ranking is exactly the
--   ranking of `p`.  Any member can therefore be made the "universal winner" — or a
--   negligible one — by changing the sampler alone.
--
--   ```lean
--   theorem Probability.PortfolioRegret.share_realizability(p : S → ℚ) (P : ℚ) (hP : 1 < P) :
--       (∀ s : S, ∑ ω ∈ univ.filter (fun ω : S => diagCost P ω s = oracleCost (diagCost P) ω),
--           p ω = p s) ∧
--       (∀ s : S, EV p (fun ω => diagCost P ω s) = p s + (∑ ω, p ω - p s) * P) ∧
--       (∀ s t : S, p t ≤ p s → EV p (fun ω => diagCost P ω s) ≤ EV p (fun ω => diagCost P ω t)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PortfolioShareRealizability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PortfolioShareRealizability.lean#L63

-- Thm stub generated from Probability/PortfolioShareRealizability.lean
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

theorem Probability.PortfolioRegret.share_realizability(p : S → ℚ) (P : ℚ) (hP : 1 < P) :
    (∀ s : S, ∑ ω ∈ univ.filter (fun ω : S => diagCost P ω s = oracleCost (diagCost P) ω),
        p ω = p s) ∧
    (∀ s : S, EV p (fun ω => diagCost P ω s) = p s + (∑ ω, p ω - p s) * P) ∧
    (∀ s t : S, p t ≤ p s → EV p (fun ω => diagCost P ω s) ≤ EV p (fun ω => diagCost P ω t)) := by sorry
