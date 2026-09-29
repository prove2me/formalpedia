-- Prove2me | solution 1 for CollatzParity.parityWord_injective_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:44:55.386887+00:00
-- url     : https://prove2.me/submissions/ccabef2d-7102-4c95-ae19-fd0facc4fe7f

-- Sol generated from MachineLearning/CollatzSpectral/ParityBijection.lean
import Mathlib
import Definitions.Def_MachineLearning_CollatzSpectral_ParityBijection
import Theorems.Thm_CollatzParity_terras
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



lemma parityWord_succ (k n : ℕ) :
    parityWord (k + 1) n = parityWord k n + pbit n k * 2 ^ k := by
  unfold parityWord; rw [Finset.sum_range_succ]


/-! ## §2. The exact transport formula -/



/-- The first `k` parity bits are a function of `n mod 2^k`. -/
theorem pbit_period (k n m j : ℕ) (hj : j < k) : pbit (n + 2 ^ k * m) j = pbit n j :=
  (terras k n m).2 j hj



/-- **Bit-flip lemma.** Adding `2^k` flips the `k`-th parity bit, because
`3^s` is odd. This is the injectivity engine. -/
theorem pbit_flip (k n : ℕ) : pbit (n + 2 ^ k) k ≠ pbit n k := by
  have h := (terras k n 1).1
  simp only [mul_one] at h
  unfold pbit
  rw [h]
  have hodd : Odd (3 ^ onesCount k n) := Odd.pow (by decide)
  rw [Nat.odd_iff] at hodd
  omega

/-! ## §3. The bijection -/

/-- Parity words of length `k` are exactly the naturals `< 2^k`. -/
theorem parityWord_lt (k n : ℕ) : parityWord k n < 2 ^ k := by
  induction k with
  | zero => simp [parityWord]
  | succ k ih =>
    rw [parityWord_succ]
    have h0 := pbit_le_one n k
    have h1 : pbit n k * 2 ^ k ≤ 2 ^ k := by
      nlinarith [pow_pos (by norm_num : (0:ℕ) < 2) k]
    have h2 : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    omega







/-! ## §4. Extremal parity prefixes -/







open CollatzParity in
theorem solution(k : ℕ) : ∀ n n' : ℕ,
    parityWord k n = parityWord k n' → n % 2 ^ k = n' % 2 ^ k := by
  induction k with
  | zero => intro n n' _; omega
  | succ k ih =>
    have main : ∀ n n' : ℕ, n ≤ n' → parityWord (k + 1) n = parityWord (k + 1) n' →
        n % 2 ^ (k + 1) = n' % 2 ^ (k + 1) := by
      intro n n' hle h
      rw [parityWord_succ, parityWord_succ] at h
      have h1 := parityWord_lt k n
      have h2 := parityWord_lt k n'
      have hb1 := pbit_le_one n k
      have hb2 := pbit_le_one n' k
      have hw : parityWord k n = parityWord k n' ∧ pbit n k = pbit n' k := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb1 with e1 | e1 <;>
          rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb2 with e2 | e2 <;>
            rw [e1, e2] at h ⊢ <;> omega
      have hmod : n ≡ n' [MOD 2 ^ k] := ih n n' hw.1
      obtain ⟨c, hc⟩ : ∃ c, n' = n + 2 ^ k * c := by
        obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
        exact ⟨c, by omega⟩
      rcases Nat.even_or_odd c with hce | hco
      · obtain ⟨d, hd⟩ := hce
        have he : n' = n + 2 ^ (k + 1) * d := by subst hc; rw [hd]; ring
        subst he; simp [Nat.add_mul_mod_self_left]
      · exfalso
        obtain ⟨d, hd⟩ := hco
        have hn' : n' = (n + 2 ^ k) + 2 ^ (k + 1) * d := by subst hc; rw [hd]; ring
        have hEq : pbit n' k = pbit (n + 2 ^ k) k := by
          rw [hn']; exact pbit_period (k + 1) (n + 2 ^ k) d k (by omega)
        exact pbit_flip k n (by rw [← hEq, ← hw.2])
    intro n n' h
    rcases le_total n n' with hle | hle
    · exact main n n' hle h
    · exact (main n' n hle h.symm).symm
