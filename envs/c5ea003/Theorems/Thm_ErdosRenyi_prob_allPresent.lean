-- Prove2me | Theorems.Thm_ErdosRenyi_prob_allPresent
-- name    : ErdosRenyi.prob_allPresent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:30:14.201948+00:00
-- url     : https://prove2.me/theorems/2b8f62fc-72c0-4421-9511-14a8c473c737
-- title:
--   Independence.
-- statement:
--   **Independence.** The probability that all edges of `S` are present is `p ^ |S|`.
--
--   ```lean
--   theorem ErdosRenyi.prob_allPresent(p : ℝ) (S : Finset E) :
--       prob p (allPresent S) = p ^ S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ErdosRenyi/Model.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ErdosRenyi/Model.lean#L105

-- Thm stub generated from Algebra/ErdosRenyi/Model.lean
import Mathlib
import Definitions.Def_Algebra_ErdosRenyi_Model
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

open ErdosRenyi

variable {E : Type*} [Fintype E] [DecidableEq E]








set_option maxHeartbeats 2000000 in

theorem ErdosRenyi.prob_allPresent(p : ℝ) (S : Finset E) :
    prob p (allPresent S) = p ^ S.card := by sorry
