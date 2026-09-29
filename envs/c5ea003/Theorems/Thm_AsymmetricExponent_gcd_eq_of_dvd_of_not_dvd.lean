-- Prove2me | Theorems.Thm_AsymmetricExponent_gcd_eq_of_dvd_of_not_dvd
-- name    : AsymmetricExponent.gcd_eq_of_dvd_of_not_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:23.235879+00:00
-- url     : https://prove2.me/theorems/2cf1cde7-b1ad-4be1-a0c8-e5cbb36c6834
-- title:
--   If `d ∣ m` and the prime `r` does not divide `m`, then `gcd(m, d*r) = d`.
-- statement:
--   If `d ∣ m` and the prime `r` does not divide `m`, then `gcd(m, d*r) = d`.
--
--   ```lean
--   theorem AsymmetricExponent.gcd_eq_of_dvd_of_not_dvd{m d r : ℕ} (hr : r.Prime) (hdm : d ∣ m)
--       (hrm : ¬ r ∣ m) : Nat.gcd m (d * r) = d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/CRTBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/CRTBarrier.lean#L33

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

theorem AsymmetricExponent.gcd_eq_of_dvd_of_not_dvd{m d r : ℕ} (hr : r.Prime) (hdm : d ∣ m)
    (hrm : ¬ r ∣ m) : Nat.gcd m (d * r) = d := by sorry
