-- Prove2me | solution 1 for Round11.mobRaw_eq_of_lt_dstar
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:42:25.801733+00:00
-- url     : https://prove2.me/submissions/58f8ee9e-07bb-449b-a8fc-1556f9418067

-- Sol generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_fpr_eq_one_of_lt_dstar
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



/-- Sum of the Möbius function over the divisors of `n`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, moebius d = if n = 1 then 1 else 0 := by
  have h : ((moebius * ↑zeta : ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rwa [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h










open Round11 in
theorem solution{p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hd : 0 < d) (hlt : d < min (ordAt b p) (ordAt b q)) :
    mobRaw b (p * q) d = if d = 1 then 1 else 0 := by
  have hcongr : ∀ c ∈ d.divisors,
      moebius (d / c) * ((fpr b (p * q) c : ℕ) : ℤ) = moebius (d / c) := by
    intro c hc
    have hcd : c ∣ d := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    have hcle : c ≤ d := Nat.le_of_dvd hd hcd
    rw [fpr_eq_one_of_lt_dstar hp hq hpq hb hc0 (by omega)]
    simp
  rw [mobRaw, Finset.sum_congr rfl hcongr, Nat.sum_div_divisors d (fun c => moebius c),
    sum_divisors_moebius d]
