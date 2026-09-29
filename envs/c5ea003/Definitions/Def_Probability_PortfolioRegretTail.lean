-- Prove2me | Definitions.Def_Probability_PortfolioRegretTail
-- name    : Probability_PortfolioRegretTail
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:57.845166+00:00
-- url     : https://prove2.me/theorems/8498acae-85e5-4c70-a023-e5caa388ba3d
-- title:
--   Aether Catalog definitions — Probability_PortfolioRegretTail
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PortfolioRegretTail`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PortfolioRegretTail.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_PortfolioRegretCore
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

namespace Probability.PortfolioRegret

open Finset

variable {Ω S : Type*}

/-! ## Probabilities, ratios and medians -/

/-- Probability of an event under the weights `w`. -/
def Pr [Fintype Ω] (w : Ω → ℚ) (A : Ω → Prop) [DecidablePred A] : ℚ :=
  ∑ ω ∈ univ.filter A, w ω

/-- Instancewise regret ratio of a fixed strategy against the oracle. -/
noncomputable def regretRatio [Fintype S] [Nonempty S] (cost : Ω → S → ℚ) (s : S) (ω : Ω) : ℚ :=
  cost ω s / oracleCost cost ω



/-- The two-instance tail portfolio at level `M`: strategy `0` ties the oracle on
mass `3/4` but pays `4M+4` on the remaining quarter, while strategy `1` is
uniformly expensive on the bulk. -/
def tailCost (M : ℚ) : Fin 2 → Fin 2 → ℚ := ![![1, 8 * M + 8], ![4 * M + 4, 1]]

/-- The weights of the tail portfolio: `3/4` on the bulk, `1/4` on the tail. -/
def tailW : Fin 2 → ℚ := ![3/4, 1/4]





/-! ## Layer cake and stochastic dominance -/

/-- Upper tail probability of an `ℕ`-valued cost. -/
def PrGT [Fintype Ω] (w : Ω → ℚ) (X : Ω → ℕ) (t : ℕ) : ℚ :=
  Pr w (fun ω => t < X ω)

/-- `X` is stochastically dominated by `Y`: a genuine dominance-in-distribution
statement, as opposed to a comparison of means. -/
def StochDom [Fintype Ω] (w : Ω → ℚ) (X Y : Ω → ℕ) : Prop :=
  ∀ t : ℕ, PrGT w X t ≤ PrGT w Y t




end Probability.PortfolioRegret


