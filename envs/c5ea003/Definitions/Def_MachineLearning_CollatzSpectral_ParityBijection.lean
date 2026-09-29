-- Prove2me | Definitions.Def_MachineLearning_CollatzSpectral_ParityBijection
-- name    : MachineLearning_CollatzSpectral_ParityBijection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:18.415984+00:00
-- url     : https://prove2.me/theorems/cc7e6c54-5fce-4c06-ac22-ec70e64ff236
-- title:
--   Aether Catalog definitions — MachineLearning_CollatzSpectral_ParityBijection
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.CollatzSpectral.ParityBijection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/CollatzSpectral/ParityBijection.lean by skeleton subtraction
import Mathlib
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

namespace CollatzParity

/-! ## §1. The accelerated Collatz map and its parity word -/

/-- The **accelerated Collatz map** `T n = n/2` for even `n` and `(3n+1)/2` for
odd `n`. It is the standard Collatz map with the forced even step after an odd
step already performed. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- The unaccelerated Collatz map, for comparison. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1


/-- The `j`-th parity bit of the orbit of `n` under the accelerated map. -/
def pbit (n j : ℕ) : ℕ := (T^[j] n) % 2

/-- The **parity word** of length `k`: the first `k` parity bits of the orbit of
`n`, packed little-endian into a natural number `< 2^k`. -/
def parityWord (k n : ℕ) : ℕ := ∑ j ∈ Finset.range k, pbit n j * 2 ^ j

/-- The number of odd steps among the first `k` steps of the orbit of `n`. -/
def onesCount (k n : ℕ) : ℕ := ∑ j ∈ Finset.range k, pbit n j






/-! ## §2. The exact transport formula -/







/-! ## §3. The bijection -/








/-! ## §4. Extremal parity prefixes -/






end CollatzParity


