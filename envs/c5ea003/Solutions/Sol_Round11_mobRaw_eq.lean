-- Prove2me | solution 1 for Round11.mobRaw_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:42:24.991757+00:00
-- url     : https://prove2.me/submissions/a3290053-944e-467a-8883-133e75cda460

-- Sol generated from Combinatorics/Round11CycleIndexFingerprint.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_fpr_eq_indicator
import Theorems.Thm_Round11_mob_detect
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





/-! ## The Möbius spectrum -/













open Round11 in
theorem solution{p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hbp : ¬ p ∣ b) (hbq : ¬ q ∣ b) (hd : 0 < d) :
    mobRaw b (p * q) d
      = (if d = 1 then 1 else 0)
        + ((p : ℤ) - 1) * (if ordAt b p = d then 1 else 0)
        + ((q : ℤ) - 1) * (if ordAt b q = d then 1 else 0)
        + ((p : ℤ) - 1) * ((q : ℤ) - 1) *
            (if Nat.lcm (ordAt b p) (ordAt b q) = d then 1 else 0) := by
  have hdp := ordAt_pos hp hbp
  have hdq := ordAt_pos hq hbq
  have hn0 : 0 < Nat.lcm (ordAt b p) (ordAt b q) := Nat.pos_of_ne_zero (by
    simp [Nat.lcm_eq_zero_iff]; omega)
  have pointwise : ∀ c, ((fpr b (p * q) c : ℕ) : ℤ)
      = 1 + ((p:ℤ) - 1) * (if ordAt b p ∣ c then 1 else 0)
        + ((q:ℤ) - 1) * (if ordAt b q ∣ c then 1 else 0)
        + ((p:ℤ) - 1) * ((q:ℤ) - 1) *
            (if Nat.lcm (ordAt b p) (ordAt b q) ∣ c then 1 else 0) := by
    intro c
    have hiff : (ordAt b p ∣ c ∧ ordAt b q ∣ c) ↔ Nat.lcm (ordAt b p) (ordAt b q) ∣ c :=
      ⟨fun h => Nat.lcm_dvd h.1 h.2,
       fun h => ⟨(Nat.dvd_lcm_left _ _).trans h, (Nat.dvd_lcm_right _ _).trans h⟩⟩
    rw [fpr_eq_indicator hp hq hpq hb c]
    by_cases h1 : ordAt b p ∣ c
    · by_cases h2 : ordAt b q ∣ c
      · simp only [if_pos h1, if_pos h2, if_pos (hiff.1 ⟨h1, h2⟩)]
        push_cast
        ring
      · simp only [if_pos h1, if_neg h2, if_neg (fun h => h2 (hiff.2 h).2)]
        push_cast
        ring
    · by_cases h2 : ordAt b q ∣ c
      · simp only [if_neg h1, if_pos h2, if_neg (fun h => h1 (hiff.2 h).1)]
        push_cast
        ring
      · simp only [if_neg h1, if_neg h2, if_neg (fun h => h1 (hiff.2 h).1)]
        push_cast
        ring
  rw [mobRaw]
  have hsplit : ∀ c ∈ d.divisors, moebius (d / c) * ((fpr b (p * q) c : ℕ) : ℤ)
      = moebius (d/c) * (if (1:ℕ) ∣ c then (1:ℤ) else 0)
        + ((p:ℤ)-1) * (moebius (d/c) * (if ordAt b p ∣ c then (1:ℤ) else 0))
        + ((q:ℤ)-1) * (moebius (d/c) * (if ordAt b q ∣ c then (1:ℤ) else 0))
        + ((p:ℤ)-1) * ((q:ℤ)-1) *
            (moebius (d/c) * (if Nat.lcm (ordAt b p) (ordAt b q) ∣ c then (1:ℤ) else 0)) := by
    intro c _
    rw [pointwise c]
    simp only [one_dvd, if_true]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    mob_detect 1 d one_pos hd, mob_detect _ d hdp hd, mob_detect _ d hdq hd,
    mob_detect _ d hn0 hd]
  simp [eq_comm]
