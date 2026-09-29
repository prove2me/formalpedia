-- Prove2me | Definitions.Def_Algebra_ErdosRenyi_Model
-- name    : Algebra_ErdosRenyi_Model
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:13:58.837281+00:00
-- url     : https://prove2.me/theorems/1b942ff0-27ba-40a4-9734-f3087bcd0c07
-- title:
--   Aether Catalog definitions — Algebra_ErdosRenyi_Model
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ErdosRenyi.Model`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ErdosRenyi/Model.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Erdős–Rényi random graph model `G(n, p)` — model and first moment method

We give a fully finite, measure-free formalization of the Erdős–Rényi model.
A *configuration* is an edge-indicator function `g : E → Bool`, where `E` is a
finite type of potential edges.  The `p`-biased law assigns to a configuration
`g` the weight

  `weight p g = ∏ e, (if g e then p else 1 - p)`,

i.e. each edge is independently present with probability `p`.  Probabilities of
events (finsets of configurations) and expectations of random variables are then
ordinary finite sums.

## Main results

* `ErdosRenyi.sum_weight` — the law is a probability measure: `∑ g, weight p g = 1`.
* `ErdosRenyi.prob_allPresent` — independence: the probability that every edge of
  a set `S` is present equals `p ^ |S|`.
* `ErdosRenyi.prob_allAbsent` — dually, the probability that every edge of `S` is
  absent equals `(1 - p) ^ |S|`.
* `ErdosRenyi.expectation_subgraphCount` — linearity of expectation for subgraph
  counts: the expected number of "copies" with prescribed edge sets `S i` equals
  `∑ i, p ^ |S i|`.
* `ErdosRenyi.expectation_subgraphCount_uniform` — for copies all of size `k`,
  the expected count is `(#copies) · p ^ k` (the basic first–moment quantity that
  governs subgraph thresholds).
* `ErdosRenyi.firstMoment` — the first moment method: the probability that at least
  one copy appears is at most `∑ i, p ^ |S i|`.  In particular it vanishes as the
  expected count tends to `0`, which is the "below threshold" half of every
  monotone subgraph threshold.

-- !-- Lab Notes -- !--
Hypothesis (Stage 1): the Erdős–Rényi law can be captured without any
  measure-theoretic machinery as a `p`-biased product weight on the finite cube
  `E → Bool`, and the textbook "independence" and "linearity of expectation"
  identities are then pure `Finset` algebra (`Finset.prod_univ_sum`,
  `Finset.sum_comm`).  A bolder sub-hypothesis: the same proof yields *both* the
  all-present probability `p^|S|` and the all-absent probability `(1-p)^|S|` by the
  symmetry `p ↔ 1-p`.
Experiment (Stage 2): `sum_weight` is `Finset.prod_univ_sum` specialised to the
  two-point fibres `{p, 1-p}` whose column sums are `p + (1-p) = 1`.  The
  independence identity factors the weight product over `S` and its complement and
  collapses the complement sum to `1` by the same column-sum trick.
Analysis (Stage 3): the identities hold for *every* real `p` (no `0 ≤ p ≤ 1`
  needed) — positivity is only required for the Markov inequality `firstMoment`,
  where weights must be nonnegative.  This cleanly separates the algebraic
  (combinatorial identity) content from the order-theoretic (probabilistic
  inequality) content.
Critique (Stage 4): the theorems are genuine identities/inequalities proved by
  `induction`/`Finset` manipulation, not `decide`/`rfl`; `firstMoment` is a real
  Markov bound (the engine behind "no copies below threshold").  The sharp
  *asymptotic* connectivity/giant-component thresholds are deliberately NOT claimed
  here; they are recorded in `FUTURE_DIRECTIONS.md`.
Synthesis (Stage 5): this file is the algebraic core of `G(n,p)`; the companion
  files develop the second-moment method (`SecondMoment.lean`) and concrete
  vertex/triangle expectations (`Concrete.lean`).
-/

open Finset BigOperators

namespace ErdosRenyi

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The `p`-biased weight of an edge configuration `g : E → Bool`: each present
edge contributes a factor `p`, each absent edge a factor `1 - p`. -/
noncomputable def weight (p : ℝ) (g : E → Bool) : ℝ :=
  ∏ e : E, (if g e then p else 1 - p)



/-- Probability of an event (a finset of configurations). -/
noncomputable def prob (p : ℝ) (A : Finset (E → Bool)) : ℝ := ∑ g ∈ A, weight p g

/-- Expectation of a real random variable. -/
noncomputable def expectation (p : ℝ) (X : (E → Bool) → ℝ) : ℝ :=
  ∑ g : E → Bool, weight p g * X g

/-- The event that every edge in `S` is present. -/
def allPresent (S : Finset E) : Finset (E → Bool) :=
  Finset.univ.filter (fun g => ∀ e ∈ S, g e = true)

/-- The event that every edge in `S` is absent. -/
def allAbsent (S : Finset E) : Finset (E → Bool) :=
  Finset.univ.filter (fun g => ∀ e ∈ S, g e = false)



/-- The number of "copies" present in `g`, where copy `i` occupies edge set `S i`. -/
noncomputable def subgraphCount {ι : Type*} [Fintype ι] (S : ι → Finset E)
    (g : E → Bool) : ℕ :=
  (Finset.univ.filter (fun i => ∀ e ∈ S i, g e = true)).card




end ErdosRenyi


