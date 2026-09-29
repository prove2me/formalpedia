-- Prove2me | solution 1 for GCDMoment.gcdMoment_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:57:34.234639+00:00
-- url     : https://prove2.me/submissions/26cb517e-68d7-4ec1-a50f-54c4b631e03a

import Mathlib
import Definitions.Def_Novelty_GCDMomentTraceWitness
import Definitions.Def_Novelty_GCDMomentPairInversion
import Definitions.Def_Novelty_GCDMomentMultiplicative
open GCDMoment Finset ArithmeticFunction in
theorem solution {n : ℕ} (hn : Squarefree n) (k : ℕ) :
    gcdMoment k n = ∏ p ∈ n.primeFactors, (p ^ k + p - 1) := by
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
  have hn0 : n ≠ 0 := hn.ne_zero
  have hphi : ArithmeticFunction.IsMultiplicative phiAF := by
    constructor
    · simp [phiAF]
    · intro a b hab
      exact Nat.totient_mul hab
  have hmulAF : ArithmeticFunction.IsMultiplicative (gcdMomentAF k) :=
    ArithmeticFunction.isMultiplicative_pow.mul hphi
  have hconv : ∀ (j N : ℕ), 0 < N → gcdMoment j N = (gcdMomentAF j) N := by
    intro j N hN
    rw [hsum j N hN, gcdMomentAF, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun d e => (ArithmeticFunction.pow j) d * phiAF e)]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [ArithmeticFunction.pow_apply, hd0, phiAF]
  rw [hconv k n (Nat.pos_of_ne_zero hn0), hmulAF.multiplicative_factorization _ hn0, Finsupp.prod,
    Nat.support_factorization]
  refine Finset.prod_congr rfl (fun p hpm => ?_)
  obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hpm
  have hfac1 : n.factorization p = 1 := by
    have hle := (Nat.squarefree_iff_factorization_le_one hn0).mp hn p
    have hpos : n.factorization p ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact hpm
    omega
  rw [hfac1, pow_one, ← hconv k p hpp.pos]
  have h := hone p hpp k
  have h2 := hpp.two_le
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  omega
