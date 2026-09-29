-- Prove2me | Definitions.Def_Novelty_NeuralCoding
-- name    : Novelty_NeuralCoding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:18.11454+00:00
-- url     : https://prove2.me/theorems/6537e3b2-c9e7-48b7-b6cd-78858ad16c70
-- title:
--   Aether Catalog definitions — Novelty_NeuralCoding
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCoding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCoding.lean by skeleton subtraction
import Mathlib

/-!
# Brain–Computer Interface Mathematics: Neural Coding Theorems

This file develops, from first principles, a small but interconnected theory of
**neural coding** — how a population of neurons can represent information.  The
development is a "builder" chain: each result is proved completely and later
results are stated and proved *using* the earlier ones.

## Model

A **neural code** on `N` neurons is a binary activity pattern, i.e. an element of
`Fin N → Bool` (`true` = the neuron is spiking / active, `false` = silent).  We
write `NeuralCode N` for this type.  The **support** of a code is the set of
active neurons and its **weight** (= metabolic **energy**, one unit per spike)
is the number of active neurons.

## Results (the chain)

1. `card_neuralCode` — there are exactly `2 ^ N` distinct codes: the *coding
   capacity* of `N` binary neurons is `2 ^ N`.
2. `concept_capacity_bound` — any injective encoding of a set of concepts into
   codes can distinguish at most `2 ^ N` concepts (uses 1).
3. `capacity_tight` — and `2 ^ N` concepts *can* be encoded: there is a bijection
   `Fin (2 ^ N) ≃ NeuralCode N` (uses 1).
4. `card_neuralCode_succ` — adding one neuron doubles the capacity (uses 1).
5. `weight_le` — a code activates at most `N` neurons.
6. `card_active_coord` — a fixed neuron is active in exactly half (`2 ^ (N-1)`)
   of all codes.
7. `total_weight` / `average_weight` — the *average* weight of a dense code is
   `N / 2` (uses 6): dense coding spends `N / 2` spikes per concept.
8. `card_sparse` — there are exactly `N.choose k` codes of weight `k`
   (the *sparse* codes), and in particular `card_grandmother` gives `N`
   one‑hot ("grandmother cell") codes (uses 8).
9. Population coding: `popPrecision_eq`, `popPrecision_quarter`,
   `popPrecision_antitone` — averaging `N` noisy neurons gives error `∝ 1/√N`,
   so precision improves like `√N` and quadrupling the population halves the
   error.
10. Sparse energy efficiency: `denseRate_eq`, `sparseRate_eq`,
    `sparse_more_efficient`, `sparse_rate_tendsto_atTop` — one‑hot sparse coding
    delivers `log₂ N` bits per spike versus `2` bits per spike for dense coding,
    an unbounded (`Θ(log N)`) energy‑efficiency advantage (uses 7 and 8).
11. Neural manifold hypothesis: `neural_manifold_dim_le_dof` — if population
    activity is driven linearly by `d` behavioural degrees of freedom, the
    neural manifold (the span of reachable activity) has dimension at most `d`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the information a neural population can carry is
governed by simple combinatorics of binary patterns; sparsity trades raw
capacity for energy efficiency, and the geometry of behaviour caps the geometry
of neural activity.

Experiment (Experimenter): we modelled a code as `Fin N → Bool`, counted states
exactly (`2 ^ N`), counted weight-`k` states (`N.choose k`) via a bijection with
`powersetCard`, and computed the mean weight (`N / 2`) by double counting.  The
population-coding law is the algebraic core of the variance-of-the-mean
computation, and the manifold bound is the rank–nullity bound for the linear
behaviour→activity map.

Analysis (Analyst): the binary model is deliberately lossy (no weights, no
timing) yet already yields capacity, the sparse-coding efficiency gain, and the
dimensional cap; richer models only refine these.
-/

namespace NeuralCoding

open Finset

/-- A **neural code** on `N` neurons: a binary activity pattern, `true` meaning
the neuron is active/spiking. -/
abbrev NeuralCode (N : ℕ) : Type := Fin N → Bool

/-- The set of **active** neurons of a code (its support). -/
def active {N : ℕ} (c : NeuralCode N) : Finset (Fin N) :=
  Finset.univ.filter (fun i => c i = true)

/-- The **weight** of a code: the number of active neurons.  This is also the
metabolic **energy** it costs (one unit per spike). -/
def weight {N : ℕ} (c : NeuralCode N) : ℕ := (active c).card


/-! ## 1–4. Coding capacity of `N` binary neurons -/





/-! ## 5–7. Weight, symmetry and the average (dense) energy cost -/





/-! ## 8. Sparse codes: counting weight-`k` patterns -/



/-! ## 9. Population coding: precision `∝ √N`

Model: `N` neurons each give an unbiased estimate of a continuous stimulus with
variance `v`.  Averaging `N` independent such estimates yields the *population
estimate*, whose variance is `v / N` (variance of a sum of `N` independent
copies is `N · v`; dividing the sum by `N` scales the variance by `1 / N²`).  The
achievable **precision** is the standard deviation of the population estimate. -/

/-- Variance of the population (averaged) estimate from `N` neurons, each of
variance `v`.  Written as `(N·v)/N²` to expose the variance-of-the-mean
computation; it equals `v / N` (see `popVariance_eq`). -/
noncomputable def popVariance (v : ℝ) (N : ℕ) : ℝ := (N * v) / (N : ℝ) ^ 2


/-- **Precision** of a population code: the standard deviation of the population
estimate. -/
noncomputable def popPrecision (v : ℝ) (N : ℕ) : ℝ := Real.sqrt (popVariance v N)




/-! ## 10. Sparse coding is energy efficient (`Θ(log N)` bits per spike)

Information is measured in bits, `information m = log₂ m` bits to index `m`
equiprobable concepts.  The **information rate** is bits per unit energy (per
spike).

* Dense coding uses all `2 ^ N` codes, `N` bits of information, at an average
  cost of `N / 2` spikes (`average_weight`): rate `= 2` bits/spike.
* One‑hot sparse coding uses the `N` grandmother codes (`card_grandmother`),
  `log₂ N` bits, at exactly `1` spike each: rate `= log₂ N` bits/spike.

Hence sparse coding beats dense coding once `N ≥ 5`, and its advantage grows
without bound. -/

/-- Information (in bits) needed to index `m` equiprobable concepts. -/
noncomputable def information (m : ℕ) : ℝ := Real.logb 2 m





/-! ## 11. Neural manifold hypothesis -/


end NeuralCoding


