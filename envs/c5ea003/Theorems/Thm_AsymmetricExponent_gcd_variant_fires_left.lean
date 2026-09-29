-- Prove2me | Theorems.Thm_AsymmetricExponent_gcd_variant_fires_left
-- name    : AsymmetricExponent.gcd_variant_fires_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:54.455957+00:00
-- url     : https://prove2.me/theorems/f4dfbbe1-3458-4d37-941b-9dcdc0f96978
-- title:
--   When the gcd variant fires.
-- statement:
--   **When the gcd variant fires.** For `a` coprime to `p`, the prime `p`
--   divides `a^(N-1) - 1` exactly when the multiplicative order of `a` modulo `p`
--   divides `q - 1` — the *other* prime's Fermat exponent.  This is the precise
--   "EULERGAP" firing condition for `gcd(a^(N-1) - 1, N)`.
--
--   ```lean
--   theorem AsymmetricExponent.gcd_variant_fires_left{p q a : ℕ} [Fact p.Prime] (hp : p.Prime)
--       (hq : 0 < q) (ha : Nat.Coprime a p) :
--       ((a : ZMod p) ^ (p * q - 1) = 1) ↔ orderOf (a : ZMod p) ∣ q - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/Core.lean#L138

-- Thm stub generated from Cryptography/AsymmetricExponent/Core.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core

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

open AsymmetricExponent


/-! ## The asymmetric exponent identity -/





/-! ## The same statements for the reduced quantity -/




/-! ## The exponent gcd collapse -/




/-! ## The gcd variant -/

theorem AsymmetricExponent.gcd_variant_fires_left{p q a : ℕ} [Fact p.Prime] (hp : p.Prime)
    (hq : 0 < q) (ha : Nat.Coprime a p) :
    ((a : ZMod p) ^ (p * q - 1) = 1) ↔ orderOf (a : ZMod p) ∣ q - 1 := by sorry
