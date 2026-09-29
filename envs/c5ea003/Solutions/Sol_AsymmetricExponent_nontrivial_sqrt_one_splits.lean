-- Prove2me | solution 1 for AsymmetricExponent.nontrivial_sqrt_one_splits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:26:08.577005+00:00
-- url     : https://prove2.me/submissions/2b5d072d-fd61-47cd-9ee2-52bb0fe0d494

-- Sol generated from Cryptography/AsymmetricExponent/CRTBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Theorems.Thm_AsymmetricExponent_gcd_splits_of_dvd_mul

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





open AsymmetricExponent in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (hp2 : p ≠ 2) (hq2 : q ≠ 2) {x : ℤ}
    (hsq : ((p * q : ℕ) : ℤ) ∣ (x - 1) * (x + 1))
    (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ (x - 1)) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ (x + 1)) :
    Nat.gcd (x - 1).natAbs (p * q) = p ∨ Nat.gcd (x - 1).natAbs (p * q) = q := by
  have key : ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ ((r : ℤ) ∣ (x - 1) ∧ (r : ℤ) ∣ (x + 1)) := by
    rintro r hr hr2 ⟨hu, hv⟩
    have htwo : (r : ℤ) ∣ 2 := by
      have := dvd_sub hv hu
      simpa using this
    have : r ∣ 2 := by
      have := Int.natAbs_dvd_natAbs.mpr htwo
      simpa using this
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact hr.one_lt.ne' h
    · exact hr2 h
  exact gcd_splits_of_dvd_mul hp hq hpq hsq h0 h1 (key p hp hp2) (key q hq hq2)
