-- Prove2me | solution 1 for Round11.one_lt_fpr_dstar
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:34:33.95025+00:00
-- url     : https://prove2.me/submissions/ffa9170a-a04e-4a43-ac42-a78a80b37994

-- Sol generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_fpr_eq_indicator
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
theorem solution{p q b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) :
    1 < fpr b (p * q) (min (ordAt b p) (ordAt b q)) := by
  rw [fpr_eq_indicator hp hq hpq hb]
  rcases le_total (ordAt b p) (ordAt b q) with h | h
  · have : min (ordAt b p) (ordAt b q) = ordAt b p := min_eq_left h
    rw [this, if_pos dvd_rfl]
    have := hp.two_le
    rcases (by split <;> simp : (if ordAt b q ∣ ordAt b p then q else 1) = q ∨
        (if ordAt b q ∣ ordAt b p then q else 1) = 1) with h' | h' <;> rw [h']
    · nlinarith [hq.two_le]
    · omega
  · have : min (ordAt b p) (ordAt b q) = ordAt b q := min_eq_right h
    rw [this, if_pos dvd_rfl]
    have := hq.two_le
    rcases (by split <;> simp : (if ordAt b p ∣ ordAt b q then p else 1) = p ∨
        (if ordAt b p ∣ ordAt b q then p else 1) = 1) with h' | h' <;> rw [h']
    · nlinarith [hp.two_le]
    · omega
