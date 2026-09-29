-- Prove2me | solution 1 for NeuralCodeCapacity.hamming_bound_maxCodeSize
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:46:09.809772+00:00
-- url     : https://prove2.me/submissions/37bc5149-a38f-4ef3-aa92-fec44f4b277c

-- Sol generated from Novelty/NeuralCodeCapacityBounds.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Theorems.Thm_NeuralCodeCapacity_card_ball_eq_card_wt_le
import Theorems.Thm_NeuralCodeCapacity_card_wt_eq
import Theorems.Thm_NeuralCodeCapacity_exists_maxCodeSize

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

open NeuralCodeCapacity

open Finset






/-! ## Hamming balls and their volume -/







private lemma card_wt_le (N r : ℕ) :
    (Finset.univ.filter (fun z : NeuralCode N => wt z ≤ r)).card
      = ∑ k ∈ Finset.range (r + 1),
          (Finset.univ.filter (fun z : NeuralCode N => wt z = k)).card := by
  rw [← Finset.card_biUnion]
  · congr 1
    ext z; simp only [mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
    exact ⟨fun h => ⟨wt z, by omega, rfl⟩, fun ⟨k, hk, hz⟩ => by omega⟩
  · intro i _ j _ hij
    simp only [Finset.disjoint_left, mem_filter]
    rintro z ⟨_, hz⟩ ⟨_, hz'⟩; exact hij (hz ▸ hz')

/-- **Volume of a Hamming ball.**  A ball of radius `r` on `N` neurons contains
exactly `∑_{k ≤ r} C(N,k)` patterns, whatever its centre. -/
theorem card_ball {N : ℕ} (c : NeuralCode N) (r : ℕ) :
    (ball c r).card = ballVolume N r := by
  rw [card_ball_eq_card_wt_le, card_wt_le, ballVolume]
  exact Finset.sum_congr rfl (fun k _ => card_wt_eq N k)

/-- The total number of patterns is `2 ^ N`: the raw capacity of `N` neurons. -/
theorem card_neuralCode (N : ℕ) :
    (Finset.univ : Finset (NeuralCode N)).card = 2 ^ N := by
  simp

/-! ## Separated codebooks and the capacity function `A(N,d)` -/











/-! ## The Gilbert–Varshamov existence bound -/


/-! ## The sphere-packing (Hamming) upper bound -/

private lemma balls_disjoint {N t : ℕ} {C : Finset (NeuralCode N)}
    (hC : Separated (2 * t + 1) C) :
    (C : Set (NeuralCode N)).PairwiseDisjoint (fun c => ball c t) := by
  intro x hx y hy hxy
  simp only [Function.onFun, Finset.disjoint_left]
  intro z hz hz'
  simp only [ball, mem_filter, mem_univ, true_and] at hz hz'
  have htri : hammingDist x y ≤ hammingDist x z + hammingDist y z := by
    simpa [hammingDist_comm] using hammingDist_triangle x z y
  have := hC x hx y hy hxy
  omega

/-- **Sphere-packing (Hamming) bound.**  A `t`-error-correcting codebook (any two
codewords at distance `≥ 2t+1`) owns disjoint balls of radius `t`, so

`|C| * ballVolume N t ≤ 2 ^ N`. -/
theorem hamming_bound {N t : ℕ} {C : Finset (NeuralCode N)}
    (hC : Separated (2 * t + 1) C) : C.card * ballVolume N t ≤ 2 ^ N := by
  classical
  have hdisj := balls_disjoint hC
  have hcard : (C.biUnion (fun c => ball c t)).card = ∑ c ∈ C, (ball c t).card :=
    Finset.card_biUnion (fun x hx y hy hxy => hdisj hx hy hxy)
  have hle : (C.biUnion (fun c => ball c t)).card ≤ 2 ^ N := by
    rw [← card_neuralCode N]
    exact Finset.card_le_card (Finset.subset_univ _)
  rw [hcard, Finset.sum_congr rfl (fun c _ => card_ball c t)] at hle
  simpa [mul_comm] using hle


/-! ## The Singleton (projection) upper bound -/




/-! ## The Plotkin bound: robustness beyond half the population -/







/-! ## Exact values of the capacity function -/







/-! ## The two-sided capacity estimate -/



/-! ## The parity-extension identity `A(N+1, 2t+2) = A(N, 2t+1)`

Adding a single **parity neuron** — one that fires exactly when an odd number of
the other neurons fire — converts a code correcting `t` errors into one of even
minimum distance `2t+2` on one more neuron, and every even-distance code arises
this way.  So an extra neuron buys *detection* of one further error but no extra
concepts. -/


















/-! ## Asymptotics: the entropy bound on ball volume and the GV rate theorem

Writing `δ = r / N` for the relative radius, the volume of a Hamming ball obeys
`ballVolume N r ≤ exp (N * H(δ))` with `H` the binary entropy (in nats).
Feeding this into Gilbert–Varshamov gives the classical **rate bound**: a
population of `N` neurons supports codebooks of rate at least `1 - H₂(δ)` bits
per neuron while tolerating `δ N` misfiring neurons. -/








open NeuralCodeCapacity in
theorem solution(N t : ℕ) :
    maxCodeSize N (2 * t + 1) * ballVolume N t ≤ 2 ^ N := by
  obtain ⟨C, hC, hcard⟩ := exists_maxCodeSize N (2 * t + 1)
  rw [← hcard]
  exact hamming_bound hC
