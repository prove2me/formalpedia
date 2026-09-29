-- Prove2me | solution 1 for NeuralCodeCapacity.card_ball_eq_card_wt_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:41:21.125856+00:00
-- url     : https://prove2.me/submissions/28bf95c2-5825-4696-9cb4-907f5b2691d3

-- Sol generated from Novelty/NeuralCodeCapacityBounds.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds

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



/-- The Hamming distance as a sum of disagreement indicators. -/
lemma hammingDist_eq_sum {N : ℕ} (x y : NeuralCode N) :
    hammingDist x y = ∑ i, (if x i = y i then 0 else 1) := by
  rw [hammingDist, Finset.card_filter]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : x i = y i <;> simp [h])



/-! ## Hamming balls and their volume -/



/-- The distance from `c` is the weight of the neuron-wise XOR with `c`. -/
lemma dist_eq_wt_xor {N : ℕ} (c x : NeuralCode N) :
    hammingDist c x = wt (fun i => xor (c i) (x i)) := by
  rw [hammingDist_eq_sum, wt]
  exact Finset.sum_congr rfl (fun i _ => by cases c i <;> cases x i <;> simp)

private lemma xor_cancel {N : ℕ} (c z : NeuralCode N) :
    (fun i => xor (c i) (xor (c i) (z i))) = z := by
  funext i; cases c i <;> cases z i <;> simp






/-! ## Separated codebooks and the capacity function `A(N,d)` -/











/-! ## The Gilbert–Varshamov existence bound -/


/-! ## The sphere-packing (Hamming) upper bound -/




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
theorem solution{N : ℕ} (c : NeuralCode N) (r : ℕ) :
    (ball c r).card = (Finset.univ.filter (fun z : NeuralCode N => wt z ≤ r)).card := by
  apply Finset.card_bij (fun x _ => (fun i => xor (c i) (x i)))
  · intro x hx
    simp only [ball, mem_filter, mem_univ, true_and] at hx ⊢
    rwa [← dist_eq_wt_xor]
  · intro a _ b _ hab
    funext i
    have := congrFun hab i
    cases c i <;> cases ha' : a i <;> cases hb' : b i <;> simp_all
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    refine ⟨(fun i => xor (c i) (z i)), ?_, xor_cancel c z⟩
    simp only [ball, mem_filter, mem_univ, true_and]
    rw [dist_eq_wt_xor, xor_cancel]
    exact hz
