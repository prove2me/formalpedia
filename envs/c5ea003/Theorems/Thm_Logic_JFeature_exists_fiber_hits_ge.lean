-- Prove2me | Theorems.Thm_Logic_JFeature_exists_fiber_hits_ge
-- name    : Logic.JFeature.exists_fiber_hits_ge
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:29:05.881129+00:00
-- url     : https://prove2.me/theorems/a3d7709b-f053-4f11-907d-5a8888366723
-- title:
--   Pigeonhole / selection floor (counting form).
-- statement:
--   **Pigeonhole / selection floor (counting form).** For any feature map `u`
--   and hit set `H` there is a value `k` whose fiber carries at least a
--   proportional share of the hits.  No randomness and no signal are involved.
--
--   ```lean
--   theorem Logic.JFeature.exists_fiber_hits_ge[Nonempty ι] (u : ι → κ) (H : Finset ι) :
--       ∃ k : κ, H.card * (univ.filter (fun i => u i = k)).card
--         ≤ (H.filter (fun i => u i = k)).card * Fintype.card ι := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/JFeatureMarginalBlindness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/JFeatureMarginalBlindness.lean#L110

-- Thm stub generated from Logic/JFeatureMarginalBlindness.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
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

open Logic.JFeature

open Finset

/-! ## Hit rates, global rate, enrichment -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]










/-! ## The selection floor: some cell always looks enriched -/


variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in

theorem Logic.JFeature.exists_fiber_hits_ge[Nonempty ι] (u : ι → κ) (H : Finset ι) :
    ∃ k : κ, H.card * (univ.filter (fun i => u i = k)).card
      ≤ (H.filter (fun i => u i = k)).card * Fintype.card ι := by sorry
