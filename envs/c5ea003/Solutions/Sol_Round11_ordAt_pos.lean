-- Prove2me | solution 1 for Round11.ordAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:34:34.58088+00:00
-- url     : https://prove2.me/submissions/4376d73c-46fd-4935-add0-603872812b3b

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





/-! ## The order seal: no information below `d* = min (ord_p b) (ord_q b)` -/





/-! ## The Möbius spectrum -/













open Round11 in
theorem solution{p b : ℕ} (hp : p.Prime) (hbp : ¬ p ∣ b) : 0 < ordAt b p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hb0 : (b : ZMod p) ≠ 0 := by
    simpa [ZMod.natCast_eq_zero_iff] using hbp
  have hpow : (b : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hb0
  have hdvd : ordAt b p ∣ p - 1 := orderOf_dvd_iff_pow_eq_one.2 hpow
  rcases Nat.eq_zero_or_pos (ordAt b p) with h | h
  · exfalso
    rw [h] at hdvd
    have := Nat.eq_zero_of_zero_dvd hdvd
    have := hp.two_le
    omega
  · exact h
