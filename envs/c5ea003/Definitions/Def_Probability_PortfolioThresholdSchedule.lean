-- Prove2me | Definitions.Def_Probability_PortfolioThresholdSchedule
-- name    : Probability_PortfolioThresholdSchedule
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:34:45.223314+00:00
-- url     : https://prove2.me/theorems/88e27f7a-f855-4361-bccb-d33774b1fe4b
-- title:
--   Aether Catalog definitions — Probability_PortfolioThresholdSchedule
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioThresholdSchedule`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioThresholdSchedule.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioDialEdge
import Definitions.Def_Probability_PortfolioRegretCore
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Threshold schedules: monotone comparative statics for portfolio scheduling

Seventh cycle of the portfolio programme, closing direction 2 of
`FUTURE_DIRECTIONS.md` ("smoothness-quantile scheduling law").

The measured cell of experiment 560 is organised by a *single hidden scalar* — the
powersmoothness of `p - 1` — and the named next experiment buys a noisy view of
that scalar with a short-capped `p - 1` probe.  If the probe's output is ordered
(a smoothness quantile), one wants to know whether the optimal schedule is a
*threshold rule* in that one number rather than an unstructured policy.  This file
proves that it is, under the exact structural hypothesis that makes it true.

* `DecreasingDifferences` — the single-crossing hypothesis: raising the observed
  quantile never raises the *relative* cost of a later portfolio member.
* `leastArgmin_monotone` — **discrete Topkis theorem**: under decreasing
  differences the least fiberwise-optimal member is a monotone function of the
  observation.
* `exists_monotone_optimal_dial` — hence some *monotone* rule attains the optimal
  dial value `dialValue`: the optimal schedule is order-structured, and searching
  monotone rules loses nothing.
* `dial_fibers_ordConnected` — the instance set on which a given member is played
  is an interval of quantiles; `monotone_two_member_upward_closed` states the
  two-member case as a genuine threshold: the second member is played exactly on
  an upward-closed set of quantiles.
* `leastArgmin_not_monotone_without_dd` — the hypothesis is not decorative: an
  explicit `2 x 2` cost matrix without decreasing differences has a
  non-monotone (hence non-threshold) optimal schedule.

The results are stated for an arbitrary finite linearly ordered observation space
and finite linearly ordered portfolio, and then specialised to the fiber values
`fiberVal` of `Probability.PortfolioDialEdge`.
-/

namespace Probability.PortfolioRegret

open Finset

variable {Ω O S : Type*}

/-! ## Least minimisers -/

open scoped Classical in
/-- The set of minimisers of `f`. -/
noncomputable def argminSet [Fintype S] (f : S → ℚ) : Finset S :=
  univ.filter (fun s => ∀ t, f s ≤ f t)

theorem mem_argminSet [Fintype S] {f : S → ℚ} {s : S} :
    s ∈ argminSet f ↔ ∀ t, f s ≤ f t := by
  classical
  simp [argminSet]

theorem argminSet_nonempty [Fintype S] [Nonempty S] (f : S → ℚ) : (argminSet f).Nonempty := by
  obtain ⟨s, -, hs⟩ := Finset.exists_min_image (univ : Finset S) f univ_nonempty
  exact ⟨s, mem_argminSet.mpr fun t => hs t (mem_univ t)⟩

/-- The smallest minimiser of `f` — the canonical tie-breaking choice. -/
noncomputable def leastArgmin [Fintype S] [LinearOrder S] [Nonempty S] (f : S → ℚ) : S :=
  (argminSet f).min' (argminSet_nonempty f)




/-! ## Discrete Topkis: monotone comparative statics -/

/-- **Single crossing / decreasing differences.**  Moving to a higher observation
never increases the cost of a later member *relative* to an earlier one: the
observation and the portfolio index are complements. -/
def DecreasingDifferences [Preorder O] [Preorder S] (f : O → S → ℚ) : Prop :=
  ∀ ⦃o o' : O⦄, o ≤ o' → ∀ ⦃s s' : S⦄, s ≤ s' → f o' s' - f o' s ≤ f o s' - f o s


/-! ## Monotone (threshold) schedules are optimal -/

/-- The canonical fiberwise-optimal rule: on each fiber play the least optimal
member. -/
noncomputable def leastDial [Fintype Ω] [DecidableEq O] [Fintype S] [LinearOrder S] [Nonempty S]
    (w : Ω → ℚ) (cost : Ω → S → ℚ) (obs : Ω → O) (o : O) : S :=
  leastArgmin (fiberVal w cost obs o)





/-! ## The hypothesis is necessary -/

/-- Two quantiles, two members, *without* decreasing differences. -/
def crossCost : Fin 2 → Fin 2 → ℚ := fun o s => if (s : ℕ) = (o : ℕ) then 1 else 0


end Probability.PortfolioRegret


