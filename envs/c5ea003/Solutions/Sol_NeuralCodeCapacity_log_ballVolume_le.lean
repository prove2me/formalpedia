-- Prove2me | solution 1 for NeuralCodeCapacity.log_ballVolume_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:43:10.409155+00:00
-- url     : https://prove2.me/submissions/79838d30-e93e-4020-84b7-81f973e60aa9

-- Sol generated from Novelty/NeuralCodeCapacityBounds.lean
import Mathlib
import Definitions.Def_Novelty_NeuralCodeCapacityBounds
import Theorems.Thm_NeuralCodeCapacity_ballVolume_mul_le_one

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

lemma ballVolume_pos (N r : ℕ) : 0 < ballVolume N r := by
  rw [ballVolume]
  exact Finset.sum_pos' (fun i _ => Nat.zero_le _) ⟨0, by simp, by simp⟩







open NeuralCodeCapacity in
theorem solution(N r : ℕ) (hr0 : 0 < r) (hr : 2 * r ≤ N) :
    Real.log (ballVolume N r) ≤ N * Real.binEntropy ((r : ℝ) / N) := by
  have hrN : r ≤ N := by omega
  have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set p : ℝ := (r : ℝ) / N with hpdef
  have hr0' : (0:ℝ) < r := by exact_mod_cast hr0
  have hp0 : 0 < p := div_pos hr0' hN0
  have hNp : (N : ℝ) * p = r := by rw [hpdef]; field_simp
  have hple : p ≤ 1 - p := by
    rw [le_sub_iff_add_le, hpdef, ← add_div, div_le_one hN0]
    have : (2 : ℝ) * r ≤ N := by exact_mod_cast hr
    linarith
  have h1p : (0:ℝ) < 1 - p := lt_of_lt_of_le hp0 hple
  have hV := ballVolume_mul_le_one N r hrN hp0.le hple
  have hVpos : (0:ℝ) < (ballVolume N r : ℝ) := by exact_mod_cast ballVolume_pos N r
  have hlog := Real.log_le_log (by positivity) hV
  rw [Real.log_one, Real.log_mul (ne_of_gt hVpos) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hcast : ((N - r : ℕ) : ℝ) = (N : ℝ) - r := by push_cast [hrN]; ring
  rw [hcast] at hlog
  have h2 : (N : ℝ) * (1 - p) = (N : ℝ) - r := by rw [mul_sub, mul_one, hNp]
  have hent : (N : ℝ) * Real.binEntropy p
      = -((r : ℝ) * Real.log p) - ((N : ℝ) - r) * Real.log (1 - p) := by
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    calc (N:ℝ) * (p * -Real.log p + (1 - p) * -Real.log (1 - p))
        = -(((N:ℝ) * p) * Real.log p) - (((N:ℝ) * (1 - p)) * Real.log (1 - p)) := by ring
      _ = -((r : ℝ) * Real.log p) - ((N : ℝ) - r) * Real.log (1 - p) := by rw [hNp, h2]
  rw [hent]
  linarith
