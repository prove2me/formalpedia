-- Prove2me | Theorems.Thm_AsymmetricExponent_gcd_splits_of_dvd_mul
-- name    : AsymmetricExponent.gcd_splits_of_dvd_mul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:30.430312+00:00
-- url     : https://prove2.me/theorems/a8b1677f-5280-4fa7-8d8e-65dc6ab47aef
-- title:
--   The general splitting lemma.
-- statement:
--   **The general splitting lemma.** Suppose `N = p*q` divides a product `u*v`,
--   neither factor of the product is divisible by `N`, and no prime of `N` divides
--   both `u` and `v`.  Then `gcd(u, N)` is a prime factor of `N`.  This is the
--   common engine behind the idempotent split and behind Rabin's square-root
--   split.
--
--   ```lean
--   theorem AsymmetricExponent.gcd_splits_of_dvd_mul{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpq : p ≠ q) {u v : ℤ} (hmul : ((p * q : ℕ) : ℤ) ∣ u * v)
--       (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ u) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ v)
--       (hpuv : ¬ ((p : ℤ) ∣ u ∧ (p : ℤ) ∣ v))
--       (hquv : ¬ ((q : ℤ) ∣ u ∧ (q : ℤ) ∣ v)) :
--       Nat.gcd u.natAbs (p * q) = p ∨ Nat.gcd u.natAbs (p * q) = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/CRTBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/CRTBarrier.lean#L86

-- Thm stub generated from Cryptography/AsymmetricExponent/CRTBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core

/-!
# Barrier 6: reading a CRT component of `Q` *is* factoring

`Core.lean` shows that `Q(a) = a^(N-1) mod N` has genuinely asymmetric CRT
components, `a^(q-1) mod p` and `a^(p-1) mod q`.  The natural hope is to read
one component off and learn something about the other prime.  This file proves
that the read itself is already equivalent to factoring.

Main results.

* `AsymmetricExponent.gcd_crt_idempotent` — any `e` with `e ≡ 1 (mod p)` and
  `e ≡ 0 (mod q)` satisfies `gcd(e, N) = q`: the CRT idempotent *is* the
  factorisation.
* `AsymmetricExponent.exists_crt_idempotent` and
  `AsymmetricExponent.crt_idempotent_iff_factor` — conversely the idempotent
  exists once the factorisation is known, so the two data are interchangeable.
* `AsymmetricExponent.componentReader_factors` — the barrier in its intended
  form: **any** procedure that returns the left CRT component of `Q` as a
  residue vanishing mod `q` yields the factor `q` from its value at the single
  point `a = 1`.
* `AsymmetricExponent.gcd_splits_of_dvd_mul` — the general splitting engine.
* `AsymmetricExponent.nontrivial_idempotent_splits` — a nontrivial idempotent
  modulo `N` splits `N`.
* `AsymmetricExponent.nontrivial_sqrt_one_splits` — Rabin's split: a nontrivial
  square root of `1` modulo `N` splits `N` as well.
-/

open AsymmetricExponent

/-! ## A gcd extraction lemma -/


/-! ## Idempotents split a semiprime -/





/-! ## Splitting lemmas: nontrivial idempotents and square roots of one -/

theorem AsymmetricExponent.gcd_splits_of_dvd_mul{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {u v : ℤ} (hmul : ((p * q : ℕ) : ℤ) ∣ u * v)
    (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ u) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ v)
    (hpuv : ¬ ((p : ℤ) ∣ u ∧ (p : ℤ) ∣ v))
    (hquv : ¬ ((q : ℤ) ∣ u ∧ (q : ℤ) ∣ v)) :
    Nat.gcd u.natAbs (p * q) = p ∨ Nat.gcd u.natAbs (p * q) = q := by sorry
