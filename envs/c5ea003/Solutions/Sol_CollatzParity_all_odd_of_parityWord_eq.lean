-- Prove2me | solution 1 for CollatzParity.all_odd_of_parityWord_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:43:26.795448+00:00
-- url     : https://prove2.me/submissions/aade4c31-15bd-479b-99d8-1eea490133a1

-- Sol generated from MachineLearning/CollatzSpectral/ParityBijection.lean
import Mathlib
import Definitions.Def_MachineLearning_CollatzSpectral_ParityBijection
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Collatz parity-vector bijection on `ℤ/2^k`

This file proves the *exact* 2-adic structure theorem underlying every spectral
statement about the Collatz map: the map sending a residue `n mod 2^k` to the
binary word recording the parities of the first `k` iterates of the accelerated
Collatz map is a **bijection** of `ℤ/2^k` onto itself.

## Why this is the right object

The companion file `MachineLearning.CollatzSpectralGap` shows that the naive
exponential sum `∑_{n ≤ N} e(ω · T(n)/n)` admits **no** spectral gap: being a
continuous function of `ω` equal to `N` at `ω = 0`, its modulus comes arbitrarily
close to `N` at irrational frequencies. The obstruction is that the frequency
variable is *archimedean*. Replacing the archimedean frequency by a **2-adic**
one — i.e. Fourier analysis on the finite group `ℤ/2^k` applied to the parity
word — turns the failure into a theorem with *perfect* cancellation
(see `MachineLearning.CollatzSpectral.ParitySpectrum`).

## Main results

* `terras` — the exact affine transport formula
  `T^[k] (n + 2^k m) = T^[k] n + 3^{s_k(n)} m`, together with invariance of the
  first `k` parity bits under `n ↦ n + 2^k m`.
* `pbit_flip` — adding `2^k` flips exactly the `k`-th parity bit.
* `parityWord_injective_mod` — the parity word determines the residue mod `2^k`.
* `parityWord_bijOn` / `parityWord_surjective` — every one of the `2^k` binary
  words of length `k` is realised by exactly one residue class mod `2^k`.
* `exists_all_odd_prefix`, `exists_all_even_prefix` — the two extreme words are
  realised, so at every scale there are maximally expanding and maximally
  contracting residue classes.
-/


open Finset

open CollatzParity

/-! ## §1. The accelerated Collatz map and its parity word -/







lemma pbit_le_one (n j : ℕ) : pbit n j ≤ 1 := by unfold pbit; omega





/-! ## §2. The exact transport formula -/







/-! ## §3. The bijection -/








/-! ## §4. Extremal parity prefixes -/

/-- The all-ones word of length `k` is `2^k - 1`. -/
lemma sum_range_two_pow (k : ℕ) : ∑ j ∈ Finset.range k, 2 ^ j = 2 ^ k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega






open CollatzParity in
theorem solution(k n : ℕ) (h : parityWord k n = 2 ^ k - 1) :
    ∀ j < k, pbit n j = 1 := by
  have hgeom : ∑ j ∈ Finset.range k, 2 ^ j = 2 ^ k - 1 := sum_range_two_pow k
  have hle : ∀ j ∈ Finset.range k, pbit n j * 2 ^ j ≤ 2 ^ j := by
    intro j _
    have := pbit_le_one n j
    nlinarith [pow_pos (by norm_num : (0:ℕ) < 2) j]
  have hsum : ∑ j ∈ Finset.range k, pbit n j * 2 ^ j = ∑ j ∈ Finset.range k, 2 ^ j := by
    rw [hgeom]; exact h
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum
  intro j hj
  have hj' := this j (Finset.mem_range.mpr hj)
  have hp : (0:ℕ) < 2 ^ j := pow_pos (by norm_num) j
  nlinarith [pbit_le_one n j]
