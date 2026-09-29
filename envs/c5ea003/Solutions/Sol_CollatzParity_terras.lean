-- Prove2me | solution 1 for CollatzParity.terras
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:43:27.348993+00:00
-- url     : https://prove2.me/submissions/de04ccca-f4d6-4288-b963-3d5fab25d3b0

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









lemma onesCount_succ (k n : ℕ) : onesCount (k + 1) n = onesCount k n + pbit n k := by
  unfold onesCount; rw [Finset.sum_range_succ]



/-! ## §2. The exact transport formula -/

/-- One accelerated step under an even perturbation. -/
lemma T_add_two_mul (x m : ℕ) :
    T (x + 2 * m) = if x % 2 = 0 then T x + m else T x + 3 * m := by
  unfold T
  rcases Nat.even_or_odd x with h | h
  · have hx : x % 2 = 0 := Nat.even_iff.mp h
    simp [hx, Nat.add_mul_mod_self_left]
    omega
  · have hx : x % 2 = 1 := Nat.odd_iff.mp h
    have hx2 : (x + 2 * m) % 2 = 1 := by omega
    simp [hx, hx2]
    omega






/-! ## §3. The bijection -/








/-! ## §4. Extremal parity prefixes -/







open CollatzParity in
theorem solution(k : ℕ) : ∀ n m : ℕ,
    T^[k] (n + 2 ^ k * m) = T^[k] n + 3 ^ onesCount k n * m ∧
      ∀ j < k, pbit (n + 2 ^ k * m) j = pbit n j := by
  induction k with
  | zero => intro n m; simp [onesCount]
  | succ k ih =>
    intro n m
    have h2 : n + 2 ^ (k + 1) * m = n + 2 ^ k * (2 * m) := by ring
    obtain ⟨h1, hb⟩ := ih n (2 * m)
    rw [h2]
    have heven : 3 ^ onesCount k n * (2 * m) = 2 * (3 ^ onesCount k n * m) := by ring
    have hbits : ∀ j < k + 1, pbit (n + 2 ^ k * (2 * m)) j = pbit n j := by
      intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hb j hj'
      · unfold pbit; rw [h1, heven]; omega
    refine ⟨?_, hbits⟩
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, heven,
      T_add_two_mul]
    by_cases hp : T^[k] n % 2 = 0
    · simp [hp, onesCount_succ, pbit]
    · have hp1 : T^[k] n % 2 = 1 := by omega
      rw [if_neg hp, onesCount_succ, show pbit n k = 1 from hp1]
      ring
