-- Prove2me | Theorems.Thm_CollatzParity_terras
-- name    : CollatzParity.terras
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:02.348961+00:00
-- url     : https://prove2.me/theorems/f9bff9c1-77b6-4782-91c9-7a239280c2d9
-- title:
--   Terras' transport formula.
-- statement:
--   **Terras' transport formula.** Shifting `n` by a multiple of `2^k` leaves the
--   first `k` parity bits untouched and translates the `k`-th iterate by exactly
--   `3^{s} m`, where `s = onesCount k n` is the number of odd steps taken.
--
--   This single statement is the arithmetic heart of the whole file: it says the
--   `k`-step accelerated Collatz map is an *affine* map on each residue class
--   mod `2^k`, with slope `3^s / 2^k` — a genuinely multiplicative datum.
--
--   ```lean
--   theorem CollatzParity.terras(k : ℕ) : ∀ n m : ℕ,
--       T^[k] (n + 2 ^ k * m) = T^[k] n + 3 ^ onesCount k n * m ∧
--         ∀ j < k, pbit (n + 2 ^ k * m) j = pbit n j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CollatzSpectral/ParityBijection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CollatzSpectral/ParityBijection.lean#L108

-- Thm stub generated from MachineLearning/CollatzSpectral/ParityBijection.lean
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












/-! ## §2. The exact transport formula -/

theorem CollatzParity.terras(k : ℕ) : ∀ n m : ℕ,
    T^[k] (n + 2 ^ k * m) = T^[k] n + 3 ^ onesCount k n * m ∧
      ∀ j < k, pbit (n + 2 ^ k * m) j = pbit n j := by sorry
