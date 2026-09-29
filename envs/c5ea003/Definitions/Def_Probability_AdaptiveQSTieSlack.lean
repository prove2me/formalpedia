-- Prove2me | Definitions.Def_Probability_AdaptiveQSTieSlack
-- name    : Probability_AdaptiveQSTieSlack
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:00.076197+00:00
-- url     : https://prove2.me/theorems/eaf957d4-4dd5-4f06-9f77-0ce73000739c
-- title:
--   Aether Catalog definitions — Probability_AdaptiveQSTieSlack
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AdaptiveQSTieSlack`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AdaptiveQSTieSlack.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AdaptiveQSAllocation
import Definitions.Def_Probability_AdaptiveQSPrefixOptimality
import Definitions.Def_Probability_AdaptiveQSResidueRate
import Definitions.Def_Probability_AdaptiveQSSkipFlip
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tie-multiplicity slack of threshold deferral, and its arithmetic vanishing

`AdaptiveQSPrefixOptimality.lean` collapsed the deployment policy space: the minimum-work
quota-feasible schedule can always be taken *separated*, and a separated schedule sits
inside the dial threshold set `keepSet s r θ` at `θ = ` its own minimal rate.  That left
exactly one gap, recorded as the open direction "Tie-Multiplicity Slack of Threshold
Deferral": the threshold set retains *every* target whose rate equals `θ`, so it can be
strictly larger than the minimal schedule.

This file closes that gap.

* `tieClass` — the targets sitting exactly on the threshold.
* `keepSet_sdiff_eq_tieClass_sdiff` — the excess of the threshold set over a separated
  schedule is *exactly* the tie class outside it (an equality of sets, not a bound).
* `keepSet_card_eq_add_tie_slack` — hence the cardinality identity
  `|keepSet| = |T| + |tieClass \ T|`: the extra work done by the threshold policy is the
  tie multiplicity, nothing more.
* `keepSet_eq_of_injOn` — if the rate dial is injective on the targets there are no ties,
  and the threshold policy reproduces the minimal schedule *on the nose*.
* `periodRate_injOn_admissible` — the arithmetic input: on a factor base of admissible odd
  primes the exact rate `2/p` is injective, because `p ↦ 2/p` is.
* `factorBase_threshold_exactly_minimal` — the capstone: on such a factor base, whenever a
  relation quota is attainable there is a threshold whose retained set meets the quota, has
  the *minimum possible* cardinality among all quota-feasible schedules, and has throughput
  at least that of sieving the whole factor base.
* Lab note `labnote_tie_slack_is_one`: a three-target instance with a genuine tie, where the
  threshold policy does one unit of work more than the optimum — showing the slack term is
  not vacuous and that injectivity is doing real work.
-/

namespace Probability.AdaptiveQS

open Finset

variable {ι : Type*} [DecidableEq ι]

/-! ## The tie class of a threshold -/

/-- The targets whose rate is exactly the threshold: the only place where a threshold
policy can do more work than a minimal schedule. -/
noncomputable def tieClass (s : Finset ι) (r : ι → ℝ) (θ : ℝ) : Finset ι :=
  s.filter (fun i => r i = θ)




/-! ## The arithmetic case: rates `2/p` are pairwise distinct -/

/-- A factor base is **admissible for `N`** when each of its members is an odd prime
that does not divide `N` and for which `N` is a quadratic residue — exactly the primes
with nonzero per-period rate. -/
def AdmissibleFB (N : ℤ) (FB : Finset ℕ) : Prop :=
  ∀ p ∈ FB, p.Prime ∧ p ≠ 2 ∧ ((N : ZMod p) ≠ 0) ∧ IsSquare ((N : ZMod p))



/-! ## Lab note — the slack is real when rates tie

Rates `(3, 3, 1)` on the three targets `{0, 1, 2}` and quota `Q = 3`.  The minimum-work
schedule is a single target, but the threshold at `θ = 3` must retain both targets of rate
`3`: the tie multiplicity is `1`, and the threshold policy does one unit of work more than
the optimum.  This is exactly the term that `keepSet_card_eq_add_tie_slack` isolates, and
that `periodRate_injOn_admissible` rules out arithmetically. -/

/-- The lab-note rate vector `(3, 3, 1)` — two targets tie at the top. -/
noncomputable def tieLabRate : ℕ → ℝ := fun i => if i = 0 then 3 else if i = 1 then 3 else 1



end Probability.AdaptiveQS


