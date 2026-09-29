-- Prove2me | solution 1 for NeuralCodeCapacity.ballVolume_mul_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:41:20.300632+00:00
-- url     : https://prove2.me/submissions/71e7adb6-23a1-4726-a4c0-c6c12aecef63

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






/-! ## Hamming balls and their volume -/










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


/-- Bernoulli weights decrease with the number of successes when `p ≤ 1/2`. -/
private lemma bernoulli_term_anti {N k r : ℕ} (hkr : k ≤ r) (hrN : r ≤ N) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : p ≤ 1 - p) :
    p ^ r * (1 - p) ^ (N - r) ≤ p ^ k * (1 - p) ^ (N - k) := by
  have h1p : (0:ℝ) ≤ 1 - p := le_trans hp0 hp
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkr
  have hNk : N - k = (N - (k + j)) + j := by omega
  rw [hNk, pow_add, pow_add]
  have hpj : p ^ j ≤ (1 - p) ^ j := pow_le_pow_left₀ hp0 hp j
  calc p ^ k * p ^ j * (1 - p) ^ (N - (k + j))
      ≤ p ^ k * (1 - p) ^ j * (1 - p) ^ (N - (k + j)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hpj (by positivity)
    _ = p ^ k * ((1 - p) ^ (N - (k + j)) * (1 - p) ^ j) := by ring






open NeuralCodeCapacity in
theorem solution(N r : ℕ) (hr : r ≤ N) {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 - p) :
    (ballVolume N r : ℝ) * (p ^ r * (1 - p) ^ (N - r)) ≤ 1 := by
  have h1p : (0:ℝ) ≤ 1 - p := le_trans hp0 hp
  have hsub : Finset.range (r + 1) ⊆ Finset.range (N + 1) := by
    intro k hk; simp only [Finset.mem_range] at *; omega
  have hbinom : ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) = 1 := by
    have h := add_pow p (1 - p) N
    simp only [add_sub_cancel, one_pow] at h
    conv_rhs => rw [h]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  calc (ballVolume N r : ℝ) * (p ^ r * (1 - p) ^ (N - r))
      = ∑ k ∈ Finset.range (r + 1), (N.choose k : ℝ) * (p ^ r * (1 - p) ^ (N - r)) := by
        rw [ballVolume]; push_cast; rw [Finset.sum_mul]
    _ ≤ ∑ k ∈ Finset.range (r + 1), (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        simp only [Finset.mem_range] at hk
        exact mul_le_mul_of_nonneg_left (bernoulli_term_anti (by omega) hr hp0 hp) (by positivity)
    _ ≤ ∑ k ∈ Finset.range (N + 1), (N.choose k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ = 1 := hbinom
