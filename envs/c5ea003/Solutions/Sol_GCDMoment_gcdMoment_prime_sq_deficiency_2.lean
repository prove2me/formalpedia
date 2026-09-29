-- Prove2me | solution 2 for GCDMoment.gcdMoment_prime_sq_deficiency
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:36:18.03047+00:00
-- url     : https://prove2.me/submissions/fa00d267-00dd-4977-b84d-731aa7825370

import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative
open GCDMoment Finset ArithmeticFunction in
theorem solution {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    gcdMoment k (p ^ 2) + (p - 1) * (p ^ k - 1) = gcdMoment k p ^ 2 := by
  have hfiber : ∀ (n d : ℕ), 0 < n → d ∣ n →
      ((Finset.range n).filter (fun x => Nat.gcd n x = d)).card = (n / d).totient := by
    intro n d hn hdvd
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
    rw [Nat.totient_eq_card_coprime]
    refine Finset.card_bij' (fun x _ => x / d) (fun y _ => d * y) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
      obtain ⟨hxn, hgcd⟩ := hx
      have hdx : d ∣ x := hgcd ▸ Nat.gcd_dvd_right n x
      refine ⟨Nat.div_lt_div_of_lt_of_dvd hdvd hxn, ?_⟩
      have := Nat.coprime_div_gcd_div_gcd (m := n) (n := x) (by rw [hgcd]; exact hd)
      rwa [hgcd] at this
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
      obtain ⟨hyn, hcop⟩ := hy
      refine ⟨?_, ?_⟩
      · calc d * y < d * (n / d) := mul_lt_mul_of_pos_left hyn hd
          _ = n := Nat.mul_div_cancel' hdvd
      · rw [← Nat.mul_div_cancel' hdvd, Nat.gcd_mul_left, hcop, mul_one]
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      have hdx : d ∣ x := hx.2 ▸ Nat.gcd_dvd_right n x
      exact Nat.mul_div_cancel' hdx
    · intro y _
      exact Nat.mul_div_cancel_left y hd
  have hsum : ∀ (k n : ℕ), 0 < n → gcdMoment k n = ∑ d ∈ n.divisors, d ^ k * (n / d).totient := by
    intro k n hn
    unfold gcdMoment
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun x => Nat.gcd n x) (t := n.divisors)
      (fun x _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n x, hn.ne'⟩) (fun x => Nat.gcd n x ^ k)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    have hconst : ∑ x ∈ (Finset.range n).filter (fun x => Nat.gcd n x = d), Nat.gcd n x ^ k
        = ∑ _x ∈ (Finset.range n).filter (fun x => Nat.gcd n x = d), d ^ k := by
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [(Finset.mem_filter.mp hx).2]
    rw [hconst, Finset.sum_const, hfiber n d hn hdvd, smul_eq_mul, mul_comm]
  have hpp : ∀ (p : ℕ), p.Prime → ∀ (e k : ℕ),
      gcdMoment k (p ^ e) = ∑ i ∈ Finset.range (e + 1), p ^ (i * k) * (p ^ (e - i)).totient := by
    intro p hp e k
    rw [hsum k (p ^ e) (pow_pos hp.pos e), Nat.divisors_prime_pow hp, Finset.sum_map]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    simp only [Function.Embedding.coeFn_mk]
    rw [← pow_mul, Nat.pow_div (by omega) hp.pos]
  have hone : ∀ (p : ℕ), p.Prime → ∀ k : ℕ, gcdMoment k p + 1 = p ^ k + p := by
    intro p hp k
    have h1 : gcdMoment k (p ^ 1) = ∑ i ∈ Finset.range 2, p ^ (i * k) * (p ^ (1 - i)).totient :=
      hpp p hp 1 k
    rw [pow_one] at h1
    rw [h1]
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [Nat.zero_mul, pow_zero, Nat.sub_zero, one_mul, Nat.sub_self, Nat.totient_one,
      mul_one, Nat.one_mul, pow_one]
    rw [Nat.totient_prime hp]
    have := hp.two_le
    omega
  have hppz : ∀ (p : ℕ), p.Prime → ∀ (e k : ℕ), (gcdMoment k (p ^ e) : ℤ)
      = ∑ i ∈ Finset.range (e + 1), (p : ℤ) ^ (i * k) * ((p ^ (e - i)).totient : ℤ) := by
    intro p hp e k
    rw [hpp p hp e k]
    push_cast
    ring
  have htotz : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, 1 ≤ j →
      ((p ^ j).totient : ℤ) = (p : ℤ) ^ (j - 1) * ((p : ℤ) - 1) := by
    intro p hp j hj
    rw [Nat.totient_prime_pow hp hj]
    have h1 : 1 ≤ p := hp.one_le
    push_cast [Nat.cast_sub h1]
    ring
  have hG1z : ∀ (p : ℕ), p.Prime → ∀ k : ℕ, (gcdMoment k p : ℤ) = (p : ℤ) ^ k + (p : ℤ) - 1 := by
    intro p hp k
    have h := hone p hp k
    have hz : ((gcdMoment k p : ℕ) : ℤ) + 1 = ((p ^ k : ℕ) : ℤ) + (p : ℤ) := by
      exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) h
    push_cast at hz
    linarith
  have hG2 : (gcdMoment k (p ^ 2) : ℤ)
      = (p : ℤ) ^ (2 * k) + (p : ℤ) ^ k * ((p : ℤ) - 1) + (p : ℤ) * ((p : ℤ) - 1) := by
    rw [hppz p hp 2 k, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      htotz p hp 2 (by norm_num), htotz p hp 1 (by norm_num)]
    norm_num
    ring
  have h2 := hp.two_le
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  zify [show 1 ≤ p by omega, hpk]
  rw [hG1z p hp k, hG2]
  ring
