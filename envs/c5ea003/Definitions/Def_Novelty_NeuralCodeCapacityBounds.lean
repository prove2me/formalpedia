-- Prove2me | Definitions.Def_Novelty_NeuralCodeCapacityBounds
-- name    : Novelty_NeuralCodeCapacityBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:33:00.302469+00:00
-- url     : https://prove2.me/theorems/ba26fc95-33c4-427c-a62d-2b36291d8d8c
-- title:
--   Aether Catalog definitions — Novelty_NeuralCodeCapacityBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.NeuralCodeCapacityBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/NeuralCodeCapacityBounds.lean by skeleton subtraction
import Mathlib

/-!
# Neural Coding: the Exact Capacity Function of Noise-Tolerant Populations

A **neural code** on `N` neurons is a binary activity pattern
`NeuralCode N = Fin N → Bool`.  A population that must still tell two concepts
apart after `d - 1` of its neurons misfire may only use a set of patterns that
is **`d`-separated**: any two distinct patterns differ on at least `d` neurons.
The central quantity is therefore the *robust capacity*

`maxCodeSize N d = A(N, d) :=` the largest size of a `d`-separated codebook.

The raw capacity theorem `A(N,1) = 2 ^ N` says `N` binary neurons represent at
most (and exactly) `2 ^ N` concepts.  This file determines how that number
degrades as noise tolerance grows, by proving matching lower and upper bounds
for `A(N,d)` and computing it exactly at the ends of the range.

## Main results

* `card_ball` — a Hamming ball of radius `r` contains `ballVolume N r =
  ∑_{k ≤ r} C(N,k)` patterns, independently of its centre.
* `gilbert_varshamov` — **existence**: `2 ^ N ≤ A(N,d) * ballVolume N (d-1)`.
  Robust codebooks of guaranteed size exist; the proof is a greedy/maximality
  argument.
* `hamming_bound_maxCodeSize` — **sphere packing**: `A(N,2t+1) * ballVolume N t
  ≤ 2 ^ N`.
* `singleton_bound_maxCodeSize` — **projection**: `A(N,d) ≤ 2 ^ (N + 1 - d)`.
* `plotkin_double_count` and `plotkin_bound` — **Plotkin**: for a `d`-separated
  codebook with `N < 2d`, `|C| * (2d - N) ≤ 2d`.  Beyond half the population,
  robustness collapses capacity to a constant.
* `capacity_sandwich` — the two-sided bound
  `2 ^ N ≤ A(N,2t+1) * ballVolume N (2t)` and `A(N,2t+1) * ballVolume N t ≤ 2^N`.
* `maxCodeSize_parity_extension` — **parity-extension identity**:
  `A(N+1, 2t+2) = A(N, 2t+1)`.  A neuron devoted to parity buys one further unit
  of error *detection* but not one extra concept.
* Exact values: `maxCodeSize_one` (`A(N,1) = 2^N`), `maxCodeSize_two`
  (`A(N+1,2) = 2^N`), `maxCodeSize_self` (`A(N,N) = 2` for `N ≥ 1`),
  `maxCodeSize_succ_self` (`A(N,N+1) = 1`), and `maxCodeSize_antitone`.

* `ballVolume_mul_le_one` and `log_ballVolume_le` — the entropy estimate
  `log (ballVolume N r) ≤ N * H(r/N)` for `r/N ≤ 1/2`.
* `gilbert_varshamov_rate` and `gilbert_varshamov_rate_bits` — the asymptotic
  **rate theorem**: the best `d`-separated neural code has rate at least
  `1 - H₂(δ)` bits per neuron, `δ = (d-1)/N`.

All statements are about the exact combinatorial quantity `A(N,d)`; the small
values they predict (`A(5,3) = 4`, `A(6,4) = 4`, `A(N,2) = 2^(N-1)`, …) agree
with the exhaustive search recorded in `ComputationalEvidence.md`.
-/

namespace NeuralCodeCapacity

open Finset

/-- A **neural code** on `N` neurons: a binary activity pattern, `true` meaning
the neuron is spiking. -/
abbrev NeuralCode (N : ℕ) : Type := Fin N → Bool

/-- The **weight** (metabolic cost) of a pattern: the number of active neurons. -/
def wt {N : ℕ} (c : NeuralCode N) : ℕ := ∑ i, (if c i = true then 1 else 0)




/-! ## Hamming balls and their volume -/

/-- The **Hamming ball** of radius `r` around a pattern: all patterns reachable
by flipping at most `r` neurons. -/
def ball {N : ℕ} (c : NeuralCode N) (r : ℕ) : Finset (NeuralCode N) :=
  Finset.univ.filter (fun x => hammingDist c x ≤ r)

/-- The **volume** of a Hamming ball of radius `r` on `N` neurons. -/
def ballVolume (N r : ℕ) : ℕ := ∑ k ∈ Finset.range (r + 1), N.choose k








/-! ## Separated codebooks and the capacity function `A(N,d)` -/

/-- A codebook `C` is **`d`-separated** when distinct codewords disagree on at
least `d` neurons: the population still distinguishes the concepts after `d - 1`
neurons misfire. -/
def Separated {N : ℕ} (d : ℕ) (C : Finset (NeuralCode N)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y




open Classical in
/-- **Robust capacity** `A(N,d)`: the largest number of concepts a population of
`N` neurons can encode while keeping distinct patterns `d` neurons apart. -/
noncomputable def maxCodeSize (N d : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (NeuralCode N))).filter
    (fun C : Finset (NeuralCode N) => Separated d C)).sup Finset.card






/-! ## The Gilbert–Varshamov existence bound -/


/-! ## The sphere-packing (Hamming) upper bound -/




/-! ## The Singleton (projection) upper bound -/




/-! ## The Plotkin bound: robustness beyond half the population -/







/-! ## Exact values of the capacity function -/


/-- The two-word **repetition code**: all neurons silent, or all firing. -/
def repetitionCode (N : ℕ) : Finset (NeuralCode N) :=
  {(fun _ => false), (fun _ => true)}





/-! ## The two-sided capacity estimate -/



/-! ## The parity-extension identity `A(N+1, 2t+2) = A(N, 2t+1)`

Adding a single **parity neuron** — one that fires exactly when an odd number of
the other neurons fire — converts a code correcting `t` errors into one of even
minimum distance `2t+2` on one more neuron, and every even-distance code arises
this way.  So an extra neuron buys *detection* of one further error but no extra
concepts. -/

/-- **Puncturing**: forget the last neuron. -/
def punct {N : ℕ} (x : NeuralCode (N + 1)) : NeuralCode N := fun i => x i.castSucc

/-- **Parity extension**: append a neuron firing iff the pattern has odd weight. -/
def extend {N : ℕ} (x : NeuralCode N) : NeuralCode (N + 1) :=
  Fin.snoc x (decide (wt x % 2 = 1))
















/-! ## Asymptotics: the entropy bound on ball volume and the GV rate theorem

Writing `δ = r / N` for the relative radius, the volume of a Hamming ball obeys
`ballVolume N r ≤ exp (N * H(δ))` with `H` the binary entropy (in nats).
Feeding this into Gilbert–Varshamov gives the classical **rate bound**: a
population of `N` neurons supports codebooks of rate at least `1 - H₂(δ)` bits
per neuron while tolerating `δ N` misfiring neurons. -/







end NeuralCodeCapacity


