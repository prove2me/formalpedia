-- Prove2me | Definitions.Def_Applications_NeuralCoding_NeuralErrorCorrection
-- name    : Applications_NeuralCoding_NeuralErrorCorrection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:09.413491+00:00
-- url     : https://prove2.me/theorems/6abb648b-5edc-4415-9836-aa2a542e9f38
-- title:
--   Aether Catalog definitions — Applications_NeuralCoding_NeuralErrorCorrection
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NeuralCoding.NeuralErrorCorrection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NeuralCoding/NeuralErrorCorrection.lean by skeleton subtraction
import Mathlib

/-!
# Error-Correcting Neural Codes: the Sphere-Packing (Hamming) Bound

This file deepens the neural-coding theory of `Catalog/Novelty/NeuralCoding.lean`.
There we counted the *raw capacity* of `N` binary neurons (`2 ^ N` distinct
patterns).  Here we ask a finer question: how many patterns can a population use
if it wants to be **robust to noise**?  If two used patterns are too close in
Hamming distance, a single misfiring neuron can be mistaken for the other, so a
noise-tolerant "codebook" must keep its patterns spread apart.

## Model

A **neural code** on `N` neurons is again a binary pattern `NeuralCode N =
Fin N → Bool`.  The **Hamming distance** between two patterns is the number of
neurons on which they disagree (`hammingDist`, from Mathlib), i.e. the number of
neurons that must misfire to confuse one for the other.  A **codebook** is a
`Finset` of patterns; it **corrects `t` errors** when any two distinct codewords
are at distance `≥ 2t + 1`, so that decoding to the nearest codeword recovers the
intended pattern after up to `t` neuron flips.

## Results (the chain)

1. `hammingDist_false_eq_weight` — the Hamming distance from the silent pattern
   is the **weight** (number of active neurons).
2. `card_weight_eq` — there are exactly `N.choose k` patterns of weight `k`.
3. `card_neuralCode` / `sum_choose_weight` — there are `2 ^ N` patterns in all,
   equivalently `∑_{k} C(N,k) = 2^N` (partition by weight).
4. `ball` and `hammingDist_xor` / `ball_card_center_indep` — the number of
   patterns within distance `r` of a codeword does not depend on the codeword
   (Hamming balls are **translation invariant** under neuron-wise XOR).
5. `ball_card` — the **volume** of a Hamming ball of radius `r` is
   `∑_{k=0}^{r} C(N,k)` (uses 2 and 4).
6. `balls_pairwiseDisjoint` — the radius-`t` balls around the codewords of a
   `t`-error-correcting codebook are pairwise disjoint (triangle inequality).
7. `hamming_bound` — **the sphere-packing / Hamming bound**: a `t`-error-
   correcting codebook `C` on `N` neurons satisfies
   `|C| · (∑_{k=0}^{t} C(N,k)) ≤ 2^N` (uses 5 and 6).
8. `hamming_bound_capacity` — with `t = 0` this recovers the raw capacity bound
   `|C| ≤ 2^N`, and `singleton_error_correct_card` gives the concrete
   noise-tolerance price: a `1`-error-correcting code uses at most
   `2^N / (N+1)` of the `2^N` patterns.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): robustness costs capacity, and the exact exchange rate
is geometric — each codeword must "own" a Hamming ball of radius `t`, and these
balls tile disjointly inside the `2^N` pattern cube.

Experiment (Experimenter): we identified the pattern space with `Fin N → Bool`,
used Mathlib's `hammingDist`, proved Hamming balls are translation invariant under
neuron-wise XOR (so all balls have the same volume `∑_{k≤t} C(N,k)`), showed the
balls around distinct codewords are disjoint via the triangle inequality, and
summed with `Finset.card_biUnion`.

Analysis (Analyst): the bound is tight enough to recover the raw capacity `2^N`
at `t = 0` and yields the concrete `2^N/(N+1)` ceiling for single-error
correction; richer noise models only shrink the codebook further.
-/

namespace NeuralErrorCorrection

open Finset

/-- A **neural code** on `N` neurons: a binary activity pattern. -/
abbrev NeuralCode (N : ℕ) : Type := Fin N → Bool

/-- The **silent** pattern (all neurons off). -/
def silent (N : ℕ) : NeuralCode N := fun _ => false

/-- The **weight** of a pattern: the number of active neurons. -/
def weight {N : ℕ} (c : NeuralCode N) : ℕ :=
  (Finset.univ.filter (fun i => c i = true)).card

/-! ## 1–3. Weight, sparse counts, and total capacity -/

/-
The Hamming distance from the silent pattern is the weight.
-/

/-
**Sparse count.** There are exactly `N.choose k` patterns of weight `k`.
-/



/-! ## 4–5. Hamming balls and their volume -/

/-- The **Hamming ball** of radius `r` around a pattern `c`: all patterns within
distance `r` (correctable to `c` after at most `r` neuron flips). -/
def ball {N : ℕ} (c : NeuralCode N) (r : ℕ) : Finset (NeuralCode N) :=
  Finset.univ.filter (fun x => hammingDist c x ≤ r)

/-
Neuron-wise XOR with a fixed pattern preserves Hamming distance from that
pattern: `hammingDist c x = hammingDist (silent) (fun i => c i != x i)`.
-/

/-
**Balls are translation invariant.** The number of patterns within distance
`r` of a codeword does not depend on the codeword.
-/

/-
**Ball volume around the silent pattern.**
-/


/-! ## 6–7. Disjoint balls and the sphere-packing bound -/

/-
**Balls around codewords of a `t`-error-correcting code are disjoint.** If
any two distinct codewords are at distance `≥ 2t+1`, then their radius-`t` balls
do not overlap.
-/

/-
**Sphere-packing (Hamming) bound.** A codebook `C` on `N` neurons that
corrects `t` errors (any two distinct codewords at Hamming distance `≥ 2t+1`)
satisfies `|C| · (∑_{k=0}^{t} C(N,k)) ≤ 2^N`: noise tolerance costs capacity,
each codeword claiming a disjoint Hamming ball of volume `∑_{k≤t} C(N,k)`.
-/

/-! ## 8. Consequences -/

/-
**Zero-error special case recovers raw capacity.** With `t = 0` the Hamming
bound is exactly `|C| ≤ 2^N`.
-/

/-
**The price of single-error correction.** A codebook on `N` neurons in which
distinct codewords differ in at least `3` neurons (so any single misfire is
correctable) uses at most a `1/(N+1)` fraction of all patterns:
`|C| · (N + 1) ≤ 2^N`.
-/

end NeuralErrorCorrection


