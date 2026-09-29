-- Prove2me | solution 1 for Round11.fpr_dstar_splits
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:36:20.388385+00:00
-- url     : https://prove2.me/submissions/bf12ddd4-4e68-49a4-8fa8-dbc6ad069f68

-- Sol generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_fpr_eq_indicator
import Theorems.Thm_Round11_one_lt_fpr_dstar
import Theorems.Thm_Round11_ordAt_pos
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



/-- The nontrivial value at the order scale is a proper divisor of `N`, i.e. the
fingerprint really splits `N` there (it is `p`, `q`, or — in the degenerate case
`ord_p b = ord_q b` — all of `N`). -/
theorem fpr_dvd (b p q c : ℕ) : fpr b (p * q) c ∣ p * q := Nat.gcd_dvd_right _ _


/-! ## The Möbius spectrum -/













open Round11 in
theorem solution{p q b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hbp : ¬ p ∣ b) (hbq : ¬ q ∣ b) (hne : ordAt b p ≠ ordAt b q) :
    1 < fpr b (p * q) (min (ordAt b p) (ordAt b q)) ∧
      fpr b (p * q) (min (ordAt b p) (ordAt b q)) < p * q ∧
      fpr b (p * q) (min (ordAt b p) (ordAt b q)) ∣ p * q := by
  have hp0 : 0 < ordAt b p := ordAt_pos hp hbp
  have hq0 : 0 < ordAt b q := ordAt_pos hq hbq
  refine ⟨one_lt_fpr_dstar hp hq hpq hb, ?_, fpr_dvd _ _ _ _⟩
  rw [fpr_eq_indicator hp hq hpq hb]
  rcases lt_or_gt_of_ne hne with h | h
  · have hmin : min (ordAt b p) (ordAt b q) = ordAt b p := min_eq_left h.le
    have hnd : ¬ ordAt b q ∣ ordAt b p := fun hdvd =>
      absurd (Nat.le_of_dvd hp0 hdvd) (by omega)
    rw [hmin, if_pos dvd_rfl, if_neg hnd, mul_one]
    exact lt_mul_of_one_lt_right hp.pos hq.one_lt
  · have hmin : min (ordAt b p) (ordAt b q) = ordAt b q := min_eq_right h.le
    have hnd : ¬ ordAt b p ∣ ordAt b q := fun hdvd =>
      absurd (Nat.le_of_dvd hq0 hdvd) (by omega)
    rw [hmin, if_pos dvd_rfl, if_neg hnd, one_mul]
    exact lt_mul_of_one_lt_left hq.pos hp.one_lt
