-- Prove2me | Definitions.Def_Probability_PortfolioShareRealizability
-- name    : Probability_PortfolioShareRealizability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:42.268735+00:00
-- url     : https://prove2.me/theorems/f71b9eef-fcf0-48c0-8763-aad55e2ef381
-- title:
--   Aether Catalog definitions — Probability_PortfolioShareRealizability
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioShareRealizability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioShareRealizability.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioExp560
import Definitions.Def_Probability_PortfolioRegretCore
import Definitions.Def_Probability_PortfolioRegretTail
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

namespace Probability.PortfolioRegret

open Finset

/-! ## Sampler dependence of the winner shares -/

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- The canonical "one winner per instance class" portfolio: member `s` costs `1`
on the class it owns and the penalty `P` elsewhere. -/
def diagCost (P : ℚ) : S → S → ℚ := fun ω s => if s = ω then 1 else P




/-! ## The tail must carry the regret -/




end Probability.PortfolioRegret


