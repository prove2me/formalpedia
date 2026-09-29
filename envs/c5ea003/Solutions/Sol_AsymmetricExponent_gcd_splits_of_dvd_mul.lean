-- Prove2me | solution 1 for AsymmetricExponent.gcd_splits_of_dvd_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:24:21.665246+00:00
-- url     : https://prove2.me/submissions/9391b736-c081-48cb-bdbc-bf55af793844

-- Sol generated from Cryptography/AsymmetricExponent/CRTBarrier.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_Core
import Theorems.Thm_AsymmetricExponent_gcd_eq_of_dvd_of_not_dvd

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
    (hpq : p ≠ q) {u v : ℤ} (hmul : ((p * q : ℕ) : ℤ) ∣ u * v)
    (h0 : ¬ ((p * q : ℕ) : ℤ) ∣ u) (h1 : ¬ ((p * q : ℕ) : ℤ) ∣ v)
    (hpuv : ¬ ((p : ℤ) ∣ u ∧ (p : ℤ) ∣ v))
    (hquv : ¬ ((q : ℤ) ∣ u ∧ (q : ℤ) ∣ v)) :
    Nat.gcd u.natAbs (p * q) = p ∨ Nat.gcd u.natAbs (p * q) = q := by
  have hcopn : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hcop : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hcopn
  have hppr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hqpr : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hNdvd : ∀ x : ℤ, (p : ℤ) ∣ x → (q : ℤ) ∣ x → ((p * q : ℕ) : ℤ) ∣ x := by
    intro x hx hy
    have h := hcop.mul_dvd hx hy
    push_cast
    exact h
  have hcast : ∀ (r : ℕ) (x : ℤ), (r : ℤ) ∣ x ↔ r ∣ x.natAbs := by
    intro r x
    constructor
    · intro h
      have := Int.natAbs_dvd_natAbs.mpr h
      simpa using this
    · intro h
      have : ((r : ℤ)).natAbs ∣ x.natAbs := by simpa using h
      exact Int.natAbs_dvd_natAbs.mp this
  have hpdvd : (p : ℤ) ∣ u * v :=
    dvd_trans (by push_cast; exact Dvd.intro (q : ℤ) rfl) hmul
  have hqdvd : (q : ℤ) ∣ u * v :=
    dvd_trans (by push_cast; exact Dvd.intro_left (p : ℤ) rfl) hmul
  rcases hppr.dvd_mul.mp hpdvd with hpu | hpv
  · rcases hqpr.dvd_mul.mp hqdvd with hqu | hqv
    · exact absurd (hNdvd u hpu hqu) h0
    · left
      exact gcd_eq_of_dvd_of_not_dvd hq ((hcast p u).mp hpu)
        (fun h => hquv ⟨(hcast q u).mpr h, hqv⟩)
  · rcases hqpr.dvd_mul.mp hqdvd with hqu | hqv
    · right
      rw [Nat.mul_comm p q]
      exact gcd_eq_of_dvd_of_not_dvd hp ((hcast q u).mp hqu)
        (fun h => hpuv ⟨(hcast p u).mpr h, hpv⟩)
    · exact absurd (hNdvd v hpv hqv) h1
