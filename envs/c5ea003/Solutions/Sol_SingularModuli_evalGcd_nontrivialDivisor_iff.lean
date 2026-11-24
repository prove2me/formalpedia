-- Prove2me | solution 1 for SingularModuli.evalGcd_nontrivialDivisor_iff
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:52:24.870071+00:00
-- url     : https://prove2.me/submissions/2dfc9ca7-67a3-46fe-a3dd-a5452e4972ba

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion

/-!
# Singular Moduli Factoring, Step 1: the exact gcd criterion

The *single-step* test computes `evalGcd H j (p*q) = gcd(H.eval j, p*q)` and asks
whether it is a nontrivial divisor of `p*q`.  For distinct primes `p`, `q` this
happens exactly when `H.eval j` is divisible by exactly one of them.
-/

open SingularModuli

open Polynomial FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ} {j : ℤ}

namespace SingularModuli

private lemma dvd_prime_mul_cases {d : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (h : d ∣ p * q) : d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  have hneq : p * q ≠ 0 := Nat.mul_ne_zero hp.pos.ne' hq.pos.ne'
  by_cases hp_dvd : p ∣ d
  · by_cases hq_dvd : q ∣ d
    · have hcop : p.Coprime q :=
        hp.coprime_iff_not_dvd.mpr fun hpq =>
          hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one)
      exact Or.inr (Or.inr (Or.inr
        (Nat.dvd_antisymm h (hcop.mul_dvd_of_dvd_of_dvd hp_dvd hq_dvd))))
    · have hcop : d.Coprime q := (hq.coprime_iff_not_dvd.mpr hq_dvd).symm
      have hdp : d ∣ p := hcop.dvd_of_dvd_mul_left (by rwa [mul_comm] at h)
      exact Or.inr (Or.inl (Nat.dvd_antisymm hdp hp_dvd))
  · by_cases hq_dvd : q ∣ d
    · have hcop : d.Coprime p := (hp.coprime_iff_not_dvd.mpr hp_dvd).symm
      have hdq : d ∣ q := hcop.dvd_of_dvd_mul_left h
      exact Or.inr (Or.inr (Or.inl (Nat.dvd_antisymm hdq hq_dvd)))
    · left
      by_contra hd1
      obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hd1
      have hr_dvd : r ∣ p * q := dvd_trans hrd h
      rcases (hrp.dvd_mul.mp hr_dvd) with hrp' | hrq'
      · have hr_eq : r = p := ((Nat.dvd_prime hp).mp hrp').resolve_left hrp.ne_one
        exact hp_dvd (hr_eq ▸ hrd)
      · have hr_eq : r = q := ((Nat.dvd_prime hq).mp hrq').resolve_left hrp.ne_one
        exact hq_dvd (hr_eq ▸ hrd)

theorem solution (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    NontrivialDivisor (p * q) (evalGcd H j (p * q)) ↔
      Xor ((p : ℤ) ∣ H.eval j) ((q : ℤ) ∣ H.eval j) := by
  have hgcd_dvd_a : ((evalGcd H j (p * q) : ℕ) : ℤ) ∣ H.eval j := by
    rw [evalGcd]
    exact Int.gcd_dvd_left _ _
  have hgcd_dvd_N : evalGcd H j (p * q) ∣ p * q := by
    rw [evalGcd]
    exact Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right _ _)
  have hcopZ : IsCoprime (p : ℤ) (q : ℤ) :=
    Int.isCoprime_iff_nat_coprime.mpr
      (hp.coprime_iff_not_dvd.mpr fun hpq =>
        hne ((hq.eq_one_or_self_of_dvd p hpq).resolve_left hp.ne_one))
  constructor
  · intro hntr
    obtain ⟨hdvd, h1lt, hlt⟩ := hntr
    rcases dvd_prime_mul_cases hp hq hne hdvd with h1 | hp' | hq' | hpq
    · omega
    · have hpa : (p : ℤ) ∣ H.eval j := by
        rw [← hp']
        exact hgcd_dvd_a
      left
      refine ⟨hpa, fun hqa => ?_⟩
      have hpq_dvd_gcd : p * q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd ?_ (dvd_rfl : ((p * q : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ))
        simpa [Nat.cast_mul] using hcopZ.mul_dvd hpa hqa
      have hpq_le : p * q ≤ evalGcd H j (p * q) := Nat.le_of_dvd (by omega) hpq_dvd_gcd
      rw [hp'] at hpq_le
      nlinarith [hlt, hpq_le]
    · have hqa : (q : ℤ) ∣ H.eval j := by
        rw [← hq']
        exact hgcd_dvd_a
      right
      refine ⟨hqa, fun hpa => ?_⟩
      have hpq_dvd_gcd : p * q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd ?_ (dvd_rfl : ((p * q : ℕ) : ℤ) ∣ ((p * q : ℕ) : ℤ))
        simpa [Nat.cast_mul] using hcopZ.mul_dvd hpa hqa
      have hpq_le : p * q ≤ evalGcd H j (p * q) := Nat.le_of_dvd (by omega) hpq_dvd_gcd
      rw [hq'] at hpq_le
      nlinarith [hlt, hpq_le]
    · omega
  · intro hx
    rcases hx with ⟨hpa, hnqa⟩ | ⟨hqa, hnpa⟩
    · have hpdvd : p ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd hpa ?_
        simpa [Nat.cast_mul] using dvd_mul_right (p : ℤ) (q : ℤ)
      have hp2 : 2 ≤ p := hp.two_le
      rcases dvd_prime_mul_cases hp hq hne hgcd_dvd_N with h1 | hp' | hq' | hpq
      · exact absurd (Nat.le_of_dvd (by norm_num) (h1 ▸ hpdvd)) (by omega)
      · rw [hp']
        exact ⟨Nat.dvd_mul_right p q, hp.one_lt, by nlinarith [hp.pos, hq.one_lt]⟩
      · have hp_dvd_q : p ∣ q := hq' ▸ hpdvd
        rcases (Nat.dvd_prime hq).mp hp_dvd_q with h | h
        · exact absurd h hp.ne_one
        · exact absurd h hne
      · exact absurd (dvd_trans (by simpa [Nat.cast_mul] using dvd_mul_left (q : ℤ) (p : ℤ))
          (hpq ▸ hgcd_dvd_a)) hnqa
    · have hqdvd : q ∣ evalGcd H j (p * q) := by
        rw [evalGcd]
        refine Int.dvd_gcd hqa ?_
        simpa [Nat.cast_mul] using dvd_mul_left (q : ℤ) (p : ℤ)
      have hq2 : 2 ≤ q := hq.two_le
      rcases dvd_prime_mul_cases hp hq hne hgcd_dvd_N with h1 | hp' | hq' | hpq
      · exact absurd (Nat.le_of_dvd (by norm_num) (h1 ▸ hqdvd)) (by omega)
      · have hq_dvd_p : q ∣ p := hp' ▸ hqdvd
        rcases (Nat.dvd_prime hp).mp hq_dvd_p with h | h
        · exact absurd h hq.ne_one
        · exact absurd h.symm hne
      · rw [hq']
        exact ⟨Nat.dvd_mul_left q p, hq.one_lt, by nlinarith [hq.pos, hp.one_lt]⟩
      · exact absurd (dvd_trans (by simpa [Nat.cast_mul] using dvd_mul_right (p : ℤ) (q : ℤ))
          (hpq ▸ hgcd_dvd_a)) hnpa

end SingularModuli

open SingularModuli

theorem solution (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    NontrivialDivisor (p * q) (evalGcd H j (p * q)) ↔
      Xor ((p : ℤ) ∣ H.eval j) ((q : ℤ) ∣ H.eval j) :=
  SingularModuli.solution hp hq hne

#print axioms solution
