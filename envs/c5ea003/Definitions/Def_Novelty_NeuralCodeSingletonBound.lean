-- Prove2me | Definitions.Def_Novelty_NeuralCodeSingletonBound
-- name    : Novelty_NeuralCodeSingletonBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:53.36167+00:00
-- url     : https://prove2.me/theorems/a5bbc150-6ec8-4882-9198-542253e35c4c
-- title:
--   Aether Catalog definitions — Novelty_NeuralCodeSingletonBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCodeSingletonBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCodeSingletonBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_NeuralCoding

/-!
# Error-Correcting Neural Codes II: the Singleton Bound and Robust Capacity

This file extends the neural-coding theory of `Catalog/Novelty/NeuralCoding.lean`
(raw capacity `2 ^ N`, sparse counts, population precision) with a second,
*information-theoretic* ceiling on how many patterns a noise-tolerant population
can use.  Where `Catalog/Applications/NeuralErrorCorrection.lean` established the
geometric **sphere-packing (Hamming) bound** — each codeword owns a disjoint
Hamming ball — this file proves the complementary and logically independent
**Singleton bound**, which controls capacity through *projection* rather than
*packing*.

## Model

A **neural code** on `N` neurons is a binary activity pattern
`NeuralCode N = Fin N → Bool` (reusing the type from the capacity file).  The
**Hamming distance** between two patterns is the number of neurons on which they
disagree.  A **codebook** is a finite set `C` of patterns whose **minimum
distance** is `d` when any two distinct codewords disagree on at least `d`
neurons; such a codebook still separates its concepts after up to `d - 1`
adversarial neuron flips, and decodes them uniquely after up to `⌊(d-1)/2⌋`.

## Results (the chain)

1. `hamming_le_of_agree` — if two patterns agree on every neuron outside a set
   `S`, their Hamming distance is at most `|S|`.  This is the projection lemma
   underlying everything below.
2. `singleton_bound` — **the Singleton bound.**  A codebook on `N` neurons with
   minimum distance `d ≥ 1` uses at most `2 ^ (N + 1 - d)` patterns.  Proof:
   puncturing any `d - 1` neurons leaves an injective projection of the codebook
   into the remaining `N + 1 - d` neurons (uses 1).
3. `robust_capacity` — **capacity degrades geometrically with noise tolerance.**
   A `t`-error-correcting codebook (minimum distance `≥ 2t + 1`) uses at most
   `2 ^ (N - 2t)` of the `2 ^ N` patterns: each unit of correction guarantee
   costs two neurons of raw capacity (uses 2).
4. `singleton_message_bound` / `singleton_redundancy` — the classical `(N,k,d)`
   inequalities: a codebook carrying `k` message bits has `k ≤ N + 1 - d`, i.e.
   its redundancy `N - k` is at least `d - 1` (uses 2).
5. `full_code_attains_singleton` — the Singleton bound is **tight at `d = 1`**:
   the full pattern set achieves `2 ^ N = 2 ^ (N + 1 - 1)` (uses the capacity
   count `card_neuralCode`).
6. `repetition_attains_singleton` — the Singleton bound is **tight at `d = N`**:
   the two-word repetition code `{silent, all-firing}` has minimum distance `N`
   and `2 = 2 ^ (N + 1 - N)` codewords.  Together with 5 this exhibits tightness
   at both ends of the distance range, so the bound cannot be improved in `N`
   and `d` alone.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the sphere-packing ceiling of the companion file is
not the only obstruction to noise-tolerant capacity.  A code with large minimum
distance must "spread out" so much that projecting away a few neurons already
determines every codeword — a phenomenon of *coordinates*, not of *volume* —
giving a second, geometry-free capacity ceiling `2 ^ (N + 1 - d)`.

Experiment (Experimenter): we reused `NeuralCode N = Fin N → Bool` and Mathlib's
`hammingDist`.  The engine is `hamming_le_of_agree`: agreement off a set `S`
forces the disagreement set inside `S`, hence distance `≤ |S|`.  Puncturing an
arbitrary `(d-1)`-subset (`Finset.exists_subset_card_eq`) and mapping each
codeword to its restriction on the complement is injective on any minimum-distance
`d` codebook, so `|C|` is bounded by the `2 ^ (N + 1 - d)` restrictions
(`Finset.card_le_card_of_injOn`).

Analysis (Analyst): the Singleton and Hamming bounds are genuinely different
ceilings — Singleton is linear-algebraic (projection/rank flavour), Hamming is
metric (packing).  Both specialise to the raw capacity `2 ^ N` at zero noise
tolerance, and the repetition and full codes show Singleton is attained at the
extreme distances, so no bound depending only on `N` and `d` can beat it there.

Critique (Critic): the statement is non-vacuous — the tightness witnesses supply
codebooks that meet it with equality, so it is not a hollow inequality; the
hypotheses `1 ≤ d` and `d ≤ N + 1` are exactly the range in which the exponent
`N + 1 - d` is meaningful, and both are load-bearing (used by `omega` in the
card computation and the projection argument).

Synthesis (PI): capacity under noise is squeezed from two sides — packing volume
(Hamming) and coordinate projection (Singleton) — and the exact exchange rate for
`t`-error correction, `2 ^ N ↦ 2 ^ (N - 2t)`, falls out of the Singleton side
directly.
-/

namespace NeuralCodeSingletonBound

open Finset NeuralCoding

/-- A **neural code** on `N` neurons, reusing the capacity file's type. -/
abbrev NeuralCode (N : ℕ) : Type := NeuralCoding.NeuralCode N

/-! ## 1. The projection lemma -/


/-! ## 2. The Singleton bound -/


/-! ## 3. Robust capacity: the price of noise tolerance -/


/-! ## 4. The classical `(N, k, d)` inequalities -/



/-! ## 5–6. Tightness of the Singleton bound -/


/-- The two-word **repetition code** on `N` neurons: everyone silent, or everyone
firing. -/
def repetitionCode (N : ℕ) : Finset (NeuralCode N) :=
  {(fun _ => false), (fun _ => true)}


end NeuralCodeSingletonBound


