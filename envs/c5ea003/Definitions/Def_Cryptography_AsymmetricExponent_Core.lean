-- Prove2me | Definitions.Def_Cryptography_AsymmetricExponent_Core
-- name    : Cryptography_AsymmetricExponent_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:02:49.194009+00:00
-- url     : https://prove2.me/theorems/042ed045-64fd-48ea-b708-d0b67d519703
-- title:
--   Aether Catalog definitions — Cryptography_AsymmetricExponent_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.AsymmetricExponent.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/AsymmetricExponent/Core.lean by skeleton subtraction
import Mathlib

/-!
# The asymmetric CRT split of `a^(N-1) mod N` for a semiprime `N = p*q`

This file formalises the *structural* half of the FETQ experiment: the cheap,
factorisation-free quantity

  `Q(a) = a^(N-1) mod N`,   `N = p*q`, `p ≠ q` primes,

has an internally **asymmetric** Chinese-Remainder description:

  `Q(a) ≡ a^(q-1) (mod p)`  and  `Q(a) ≡ a^(p-1) (mod q)`.

Each CRT component of `Q` is governed by the *other* prime's Fermat exponent.
The arithmetic engine is the exponent identity `pq - 1 = (p-1)q + (q-1)`, which
is not symmetric in `p` and `q` even though `pq - 1` is.

Main results.

* `AsymmetricExponent.semiprime_exp_split` — the exponent identity.
* `AsymmetricExponent.pow_modEq_left` / `pow_modEq_right` — the asymmetric
  congruences.
* `AsymmetricExponent.fetq_mod_left` / `fetq_mod_right` — the same statements
  for the *reduced* quantity `fetq N a = a^(N-1) % N`.
* `AsymmetricExponent.fetq_unique` — `fetq N a` is the **unique** residue below
  `N` with these two components (CRT exactness; this is the "24/24 verified"
  claim, proved for all `p, q, a`).
* `AsymmetricExponent.gcd_exp_left` / `gcd_exp_right` — the exponent gcd
  collapse `gcd(N-1, p-1) = gcd(p-1, q-1) = gcd(N-1, q-1)`: the Fermat exponent
  `N-1` sees each prime only through the *common* gap `g = gcd(p-1, q-1)`.
* `AsymmetricExponent.gcd_variant_fires_left` — the gcd variant
  `gcd(a^(N-1) - 1, N)` picks up the factor `p` exactly when
  `ord_p(a) ∣ q - 1`.
-/

namespace AsymmetricExponent

/-- The FETQ quantity `Q(a) = a^(N-1) mod N`.  Note that it is defined from `N`
alone: no knowledge of the factorisation enters. -/
def fetq (N a : ℕ) : ℕ := a ^ (N - 1) % N

/-! ## The asymmetric exponent identity -/





/-! ## The same statements for the reduced quantity -/




/-! ## The exponent gcd collapse -/




/-! ## The gcd variant -/


end AsymmetricExponent


