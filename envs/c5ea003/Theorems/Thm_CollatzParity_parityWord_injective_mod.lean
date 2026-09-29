-- Prove2me | Theorems.Thm_CollatzParity_parityWord_injective_mod
-- name    : CollatzParity.parityWord_injective_mod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:13.581881+00:00
-- url     : https://prove2.me/theorems/869d240a-6570-4554-b19a-31f92efd98c5
-- title:
--   Injectivity (Terras).
-- statement:
--   **Injectivity (Terras).** The length-`k` parity word determines the residue
--   of `n` modulo `2^k`.
--
--   ```lean
--   theorem CollatzParity.parityWord_injective_mod(k : ℕ) : ∀ n n' : ℕ,
--       parityWord k n = parityWord k n' → n % 2 ^ k = n' % 2 ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CollatzSpectral/ParityBijection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CollatzSpectral/ParityBijection.lean#L178

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







/-! ## §3. The bijection -/

theorem CollatzParity.parityWord_injective_mod(k : ℕ) : ∀ n n' : ℕ,
    parityWord k n = parityWord k n' → n % 2 ^ k = n' % 2 ^ k := by sorry
