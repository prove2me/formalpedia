-- Prove2me | solution 1 for Round11.mob_detect
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:41:00.098333+00:00
-- url     : https://prove2.me/submissions/171be671-141a-4115-b8b8-71c6baf7b81c

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



/-- Sum of the Möbius function over the divisors of `n`. -/
theorem sum_divisors_moebius (n : ℕ) :
    ∑ d ∈ n.divisors, moebius d = if n = 1 then 1 else 0 := by
  have h : ((moebius * ↑zeta : ArithmeticFunction ℤ)) n = (1 : ArithmeticFunction ℤ) n := by
    rw [moebius_mul_coe_zeta]
  rwa [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h










open Round11 in
theorem solution(k d : ℕ) (hk : 0 < k) (hd : 0 < d) :
    ∑ c ∈ d.divisors, moebius (d / c) * (if k ∣ c then (1:ℤ) else 0)
      = if k = d then 1 else 0 := by
  have hd0 : d ≠ 0 := hd.ne'
  rw [← Nat.sum_div_divisors d (fun c => moebius (d / c) * (if k ∣ c then (1:ℤ) else 0))]
  have step1 : ∑ j ∈ d.divisors, moebius (d / (d / j)) * (if k ∣ d / j then (1:ℤ) else 0)
      = ∑ j ∈ d.divisors, moebius j * (if k ∣ d / j then (1:ℤ) else 0) :=
    Finset.sum_congr rfl (fun j hj => by
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hj) hd0])
  rw [step1]
  by_cases hkd : k ∣ d
  · obtain ⟨e, he⟩ := hkd
    have he0 : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · simp [h] at he; omega
      · exact h
    have key : ∀ j ∈ d.divisors, (if k ∣ d / j then (1:ℤ) else 0) = (if j ∣ e then 1 else 0) := by
      intro j hj
      have hjd := Nat.dvd_of_mem_divisors hj
      have hj0 : 0 < j := Nat.pos_of_mem_divisors hj
      have hiff : (k ∣ d / j) ↔ j ∣ e := by
        constructor
        · rintro ⟨t, ht⟩
          have hdj : d = j * (k * t) := by rw [← ht, Nat.mul_div_cancel' hjd]
          refine ⟨t, ?_⟩
          have : k * e = k * (j * t) := by rw [← he, hdj]; ring
          exact Nat.eq_of_mul_eq_mul_left hk this
        · rintro ⟨t, ht⟩
          refine ⟨t, ?_⟩
          rw [he, ht, show k * (j * t) = j * (k * t) by ring, Nat.mul_div_cancel_left _ hj0]
      simp [hiff]
    rw [Finset.sum_congr rfl (fun j hj => by rw [key j hj])]
    have hfilter : d.divisors.filter (fun j => j ∣ e) = e.divisors := by
      ext j
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_, _⟩, hje⟩; exact ⟨hje, he0.ne'⟩
      · rintro ⟨hje, _⟩
        exact ⟨⟨hje.trans ⟨k, by rw [he]; ring⟩, hd0⟩, hje⟩
    simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
    rw [hfilter, sum_divisors_moebius e]
    have hee : (e = 1) ↔ (k = d) := by
      constructor
      · rintro rfl; omega
      · rintro rfl; nlinarith
    simp [hee]
  · have hz : ∀ j ∈ d.divisors, moebius j * (if k ∣ d / j then (1:ℤ) else 0) = 0 := by
      intro j hj
      have hjd := Nat.dvd_of_mem_divisors hj
      have : ¬ k ∣ d / j := fun h => hkd (h.trans (Nat.div_dvd_of_dvd hjd))
      simp [this]
    rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
    have : k ≠ d := by rintro rfl; exact hkd dvd_rfl
    simp [this]
