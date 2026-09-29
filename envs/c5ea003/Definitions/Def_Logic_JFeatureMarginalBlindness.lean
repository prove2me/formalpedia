-- Prove2me | Definitions.Def_Logic_JFeatureMarginalBlindness
-- name    : Logic_JFeatureMarginalBlindness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:29.064224+00:00
-- url     : https://prove2.me/theorems/c96f08e1-1f88-45ba-8e7d-50bc23ca5196
-- title:
--   Aether Catalog definitions — Logic_JFeatureMarginalBlindness
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.JFeatureMarginalBlindness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/JFeatureMarginalBlindness.lean by skeleton subtraction
import Mathlib
/-
# Marginal blindness: why no `j`-feature can carry a hidden pair-carrier

This file formalises the structural reason behind the empirical verdict
`H0_CARRIER_OPEN` of the j-feature sweep (paper 248): *eight* registered
families of arithmetic features of the position index `j`
(`j mod 4`, `j mod 3`, `j mod 5`, `j mod 7`, `j mod 105`, `omega_small(j)`
terciles, smoothness of `|j - nearest square|`, `10^6`-smoothness of `j`)
all returned honest enrichment ratios `R ≤ 1.11`.

The theorems below say that this is not an accident of the particular eight
features chosen: on a sample space `α × β` where the hit set is *row balanced*
(every value of the first coordinate carries the same number of hits), **every**
cell cut out by **any** function of the first coordinate has enrichment ratio
*exactly* `1`.  Whatever new feature of `j` one invents, the marginal sweep is
guaranteed to return `R = 1`; the sweep has no power at all against carriers
that live in the *joint* (consecutive-position) structure.

Yet such carriers exist and are arbitrarily strong: for the graph of a
permutation `σ : α ≃ β` (a row-balanced hit set with one hit per row) the joint
cell "the graph itself" has hit rate `1`, i.e. enrichment `card α` over the
global rate, while all marginal cells sit at exactly `1`.

Main results.

* `exists_fiber_hits_ge` / `exists_fiber_rate_ge_globalRate` : the *selection
  floor*.  For every feature map and every hit set there is always a nonempty
  cell whose hit rate is at least the global rate; a raw "max over cells of
  `R`" statistic is therefore `≥ 1` by pure pigeonhole, with no signal
  whatsoever.  (Used in `Logic.JFeatureMaxStatistic` to show that the
  uncalibrated max test has type-I error rate `1`.)
* `rate_rowSet`, `enrich_rowSet_eq_one`, `enrich_marginal_feature_eq_one` :
  **marginal blindness**.
* `graphFinset_rowBalanced`, `rate_graphFinset`,
  `graph_joint_rate_eq_card_mul_globalRate`,
  `marginal_blind_carrier` : the joint carrier that is invisible to every
  marginal feature, with unbounded joint enrichment.
-/

namespace Logic.JFeature

open Finset

/-! ## Hit rates, global rate, enrichment -/

section Rates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hit rate of the hit set `H` inside the cell `C`. -/
noncomputable def rate (H C : Finset ι) : ℝ := ((H ∩ C).card : ℝ) / (C.card : ℝ)

/-- Global hit rate. -/
noncomputable def globalRate (H : Finset ι) : ℝ := (H.card : ℝ) / (Fintype.card ι : ℝ)

/-- Enrichment ratio of a cell against its complement — the statistic `R` of the
sweep. -/
noncomputable def enrich (H C : Finset ι) : ℝ := rate H C / rate H Cᶜ






end Rates

/-! ## The selection floor: some cell always looks enriched -/

section SelectionFloor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]




end SelectionFloor

/-! ## Marginal blindness on a product sample space -/

section MarginalBlindness

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The cell of the product space cut out by a set `S` of first coordinates:
all positions whose `j`-value lies in `S`. -/
def rowSet (S : Finset α) : Finset (α × β) := S ×ˢ (univ : Finset β)

/-- The number of hits in a row. -/
def rowHits (H : Finset (α × β)) (a : α) : ℕ := (H.filter (fun x => x.1 = a)).card

/-- `H` is *row balanced* with `m` hits per row: every value of the first
coordinate carries exactly `m` hits. -/
def RowBalanced (H : Finset (α × β)) (m : ℕ) : Prop := ∀ a : α, rowHits H a = m











/-! ### A carrier that hides from every marginal feature -/

/-- The graph of a permutation, viewed as a hit set: one hit per row. -/
def graphFinset (σ : α ≃ β) : Finset (α × β) := univ.filter (fun x => x.2 = σ x.1)






end MarginalBlindness

end Logic.JFeature


