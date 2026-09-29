-- Prove2me | solution 1 for Round11.fpr_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:33:10.054586+00:00
-- url     : https://prove2.me/submissions/7c71f0b8-0783-4023-b2fb-b71e5856d51c

-- Sol generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
/-
# Round-11 Closures, Part I: the cycle-index fingerprint and its Möbius spectrum

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypotheses **CIFINGER** / **CFSIGMA**).

For a semiprime `N = p * q` and a base `b` coprime to `N`, the *cycle-index
fingerprint* is
```
F(c) = gcd (b ^ c - 1) N .
```
The paper asserts three things about it, all of which are proved here in full:

* **Structure.** `F(c) = p^[ord_p b ∣ c] * q^[ord_q b ∣ c]`
  (`Round11.fpr_eq_indicator`).
* **The order seal.** `F(c) = 1` for every `0 < c < min (ord_p b) (ord_q b)`, and
  `F` first becomes informative exactly at `d* = min (ord_p b) (ord_q b)`
  (`Round11.fpr_eq_one_of_lt_dstar`, `Round11.one_lt_fpr_dstar`).
* **The Möbius spectrum.** The Möbius transform of the `p`-adic valuation of the
  fingerprint is the *exact indicator of the multiplicative order*:
  `∑_{c ∣ d} μ(d/c) · v_p(F c) = [ord_p b = d]`
  (`Round11.mobFinger_eq_indicator`).  Consequently the Möbius spectrum is
  supported on the two-element set `{ord_p b, ord_q b}`
  (`Round11.mobFinger_eq_zero_of_lt_dstar`): the Möbius structure is genuine but
  relocates no information below the order scale.

The last consequence is the formal content of the CFSIGMA closure: below the
order scale the fingerprint is a *constant* function of the instance, hence its
fibres cannot separate any secret statistic (see Part III).
-/

open Round11

open ArithmeticFunction Finset

/-! ## The fingerprint -/



/-! ## Basic arithmetic of the fingerprint -/

/-- Divisibility of `b^c - 1` by a prime `p` is detected by the order of `b`. -/
theorem prime_dvd_pow_sub_one_iff {p b : ℕ} (hp : p.Prime) (hb : 1 ≤ b) (c : ℕ) :
    p ∣ b ^ c - 1 ↔ ordAt b p ∣ c := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast : ((b ^ c - 1 : ℕ) : ZMod p) = (b : ZMod p) ^ c - 1 := by
    have h1 : 1 ≤ b ^ c := Nat.one_le_pow _ _ hb
    push_cast [Nat.cast_sub h1]
    ring
  rw [ordAt, ← ZMod.natCast_eq_zero_iff (b ^ c - 1) p, hcast, sub_eq_zero,
    ← orderOf_dvd_iff_pow_eq_one]

/-- The gcd of a number with a prime is the prime or one. -/
theorem gcd_prime_eq {p m : ℕ} (hp : p.Prime) :
    Nat.gcd m p = if p ∣ m then p else 1 := by
  split
  · next h => exact Nat.gcd_eq_right h
  · next h => exact Nat.Coprime.gcd_eq_one (((hp.coprime_iff_not_dvd).2 h).symm)



/-! ## The order seal: no information below `d* = min (ord_p b) (ord_q b)` -/





/-! ## The Möbius spectrum -/













open Round11 in
theorem solution{p q b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (c : ℕ) :
    fpr b (p * q) c =
      (if ordAt b p ∣ c then p else 1) * (if ordAt b q ∣ c then q else 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  rw [fpr, Nat.Coprime.gcd_mul _ hcop, gcd_prime_eq hp, gcd_prime_eq hq,
    if_congr (prime_dvd_pow_sub_one_iff hp hb c) rfl rfl,
    if_congr (prime_dvd_pow_sub_one_iff hq hb c) rfl rfl]
