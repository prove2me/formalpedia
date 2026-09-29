-- Prove2me | Theorems.Thm_AsymmetricExponent_nontrivial_sqrt_one_splits
-- name    : AsymmetricExponent.nontrivial_sqrt_one_splits
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:40.947395+00:00
-- url     : https://prove2.me/theorems/7c78e3f1-89dc-494b-9f67-3f02269842d9
-- title:
--   Rabin's split.
-- statement:
--   **Rabin's split.** A nontrivial square root of `1` modulo `N = p*q` (with
--   `p, q` odd) yields a prime factor of `N` as `gcd(x - 1, N)`.  This is the exact
--   point at which the Miller–Rabin test turns from a *witness* of compositeness
--   into a *factorisation* — and it, too, is an oracle for the CRT split.
--
--   ```lean
--   theorem AsymmetricExponent.nontrivial_sqrt_one_splits{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
--       (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {x : ℤ}
--       (hsq : ((p * q : ℕ) : ℤ) ∣ (x - 1) * (x + 1))
--       (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ (x - 1)) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ (x + 1)) :
--       Nat.gcd (x - 1).natAbs (p * q) = p ∨ Nat.gcd (x - 1).natAbs (p * q) = q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/CRTBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/CRTBarrier.lean#L146

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

theorem AsymmetricExponent.nontrivial_sqrt_one_splits{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {x : ℤ}
    (hsq : ((p * q : ℕ) : ℤ) ∣ (x - 1) * (x + 1))
    (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ (x - 1)) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ (x + 1)) :
    Nat.gcd (x - 1).natAbs (p * q) = p ∨ Nat.gcd (x - 1).natAbs (p * q) = q := by sorry
