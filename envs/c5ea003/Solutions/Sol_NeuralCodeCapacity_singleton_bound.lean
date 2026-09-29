-- Prove2me | solution 1 for NeuralCodeCapacity.singleton_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:46:11.460721+00:00
-- url     : https://prove2.me/submissions/ab500c3c-9854-4807-babb-12324fde527f

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

/-- If two patterns agree outside a set `S` of neurons they are at distance at
most `|S|`. -/
lemma hamming_le_of_agree {N : ℕ} (S : Finset (Fin N)) (x y : NeuralCode N)
    (h : ∀ i ∈ Sᶜ, x i = y i) : hammingDist x y ≤ S.card := by
  rw [hammingDist]
  apply Finset.card_le_card
  intro i hi
  simp only [mem_filter, mem_univ, true_and] at hi
  by_contra hiS
  exact hi (h i (by simp [mem_compl, hiS]))



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
theorem solution{N d : ℕ} (hd : 1 ≤ d) (hdN : d ≤ N + 1)
    {C : Finset (NeuralCode N)} (hC : Separated d C) : C.card ≤ 2 ^ (N + 1 - d) := by
  classical
  obtain ⟨S, -, hScard⟩ := Finset.exists_subset_card_eq
    (show d - 1 ≤ (univ : Finset (Fin N)).card by rw [card_univ, Fintype.card_fin]; omega)
  set f : NeuralCode N → ({i // i ∈ Sᶜ} → Bool) := fun c j => c j.1 with hf
  have hinj : Set.InjOn f C := by
    intro x hx y hy hxy
    by_contra hne
    have hagree : ∀ i ∈ Sᶜ, x i = y i := by
      intro i hi
      simpa [hf] using congrFun hxy ⟨i, hi⟩
    have h1 : d ≤ hammingDist x y := hC x hx y hy hne
    have h2 : hammingDist x y ≤ S.card := hamming_le_of_agree S x y hagree
    omega
  have hcard : C.card ≤ (univ : Finset ({i // i ∈ Sᶜ} → Bool)).card :=
    Finset.card_le_card_of_injOn f (fun a _ => mem_univ _) hinj
  rw [card_univ] at hcard
  have hcard2 : Fintype.card ({i // i ∈ Sᶜ} → Bool) = 2 ^ (N + 1 - d) := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_bool]
    congr 1
    rw [Finset.card_compl, Fintype.card_fin, hScard]
    omega
  rw [hcard2] at hcard
  exact hcard
