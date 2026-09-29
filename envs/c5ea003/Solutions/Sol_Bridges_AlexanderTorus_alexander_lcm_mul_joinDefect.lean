-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_lcm_mul_joinDefect
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T18:32:11.976966+00:00
-- url     : https://prove2.me/submissions/79785675-d075-4070-b03d-d970d61e44c3

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI

open Bridges.AlexanderTorus Polynomial Finset in
theorem solution {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    alexander (Nat.lcm M N) = joinProd M N * joinDefect M N := by
  classical
  -- the Alexander polynomial is a geometric sum in `-X`
  have halex : ∀ K : ℕ, alexander K = ∑ i ∈ range K, (-X : ℤ[X]) ^ i := by
    intro K
    unfold alexander
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- `∑_{i < dq} yⁱ = (∑_{i < d} yⁱ) (∑_{j < q} y^{dj})`
  have hprod : ∀ (y : ℤ[X]) (d q : ℕ),
      ∑ i ∈ range (d * q), y ^ i = (∑ i ∈ range d, y ^ i) * ∑ j ∈ range q, (y ^ d) ^ j := by
    intro y d q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
      congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pow_add, ← pow_mul]
      ring
  have hdvdA : ∀ d K : ℕ, d ∣ K → alexander d ∣ alexander K := by
    rintro d K ⟨q, rfl⟩
    rw [halex, halex, hprod]
    exact dvd_mul_right _ _
  have hmulA : ∀ K : ℕ, Odd K → (X + 1) * alexander K = X ^ K + 1 := by
    intro K hK
    rw [halex]
    have h := mul_neg_geom_sum (-X : ℤ[X]) K
    rw [hK.neg_pow] at h
    linear_combination h
  have hdvdA : ∀ d K : ℕ, d ∣ K → alexander d ∣ alexander K := by
    rintro d K ⟨q, rfl⟩
    rw [halex, halex, hprod]
    exact dvd_mul_right _ _
  have hmulA : ∀ K : ℕ, Odd K → (X + 1) * alexander K = X ^ K + 1 := by
    intro K hK
    rw [halex]
    have h := mul_neg_geom_sum (-X : ℤ[X]) K
    rw [hK.neg_pow] at h
    linear_combination h
  -- `A_L = ∏_{d ∣ L, d > 1} Φ_{2d}` for odd `L`
  have hfact : ∀ L : ℕ, Odd L → alexander L = ∏ d ∈ L.divisors.erase 1, cyclotomic (2 * d) ℤ := by
    intro L hL
    have hL0 : 0 < L := hL.pos
    have hdiv : (2 * L).divisors = L.divisors ∪ L.divisors.image (fun d => 2 * d) := by
      ext i
      simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨hi, -⟩
        rcases Nat.even_or_odd i with ⟨j, rfl⟩ | hodd
        · right
          refine ⟨j, ⟨?_, hL0.ne'⟩, by ring⟩
          rw [← two_mul] at hi
          exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hi
        · left
          have hcop : Nat.Coprime i 2 := (Nat.coprime_two_left.2 hodd).symm
          exact ⟨(Nat.Coprime.dvd_mul_left hcop).1 hi, hL0.ne'⟩
      · rintro (⟨hi, -⟩ | ⟨j, ⟨hj, -⟩, rfl⟩)
        · exact ⟨dvd_mul_of_dvd_right hi 2, by omega⟩
        · exact ⟨Nat.mul_dvd_mul_left 2 hj, by omega⟩
    have hdisj : Disjoint L.divisors (L.divisors.image (fun d => 2 * d)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
      have hodd : Odd (2 * j) := hL.of_dvd_nat (Nat.dvd_of_mem_divisors ha)
      exact (Nat.not_even_iff_odd.2 hodd) (even_two_mul j)
    have h2L : ∏ i ∈ (2 * L).divisors, cyclotomic i ℤ
        = (∏ d ∈ L.divisors, cyclotomic d ℤ) * ∏ d ∈ L.divisors, cyclotomic (2 * d) ℤ := by
      rw [hdiv, Finset.prod_union hdisj, Finset.prod_image (fun x _ y _ h => by omega)]
    have hXL : (X ^ L - 1 : ℤ[X]) ≠ 0 := by
      intro h
      have := congrArg (eval 0) h
      simp [hL0.ne'] at this
    have hplus : (X ^ L + 1 : ℤ[X]) = ∏ d ∈ L.divisors, cyclotomic (2 * d) ℤ := by
      have e1 := prod_cyclotomic_eq_X_pow_sub_one (show 0 < 2 * L by omega) ℤ
      have e2 := prod_cyclotomic_eq_X_pow_sub_one hL0 ℤ
      have hsub : (X ^ (2 * L) - 1 : ℤ[X]) = (X ^ L - 1) * (X ^ L + 1) := by ring
      rw [h2L, e2, hsub] at e1
      exact (mul_left_cancel₀ hXL e1).symm
    have hsplit : ∏ d ∈ L.divisors, cyclotomic (2 * d) ℤ
        = (X + 1) * ∏ d ∈ L.divisors.erase 1, cyclotomic (2 * d) ℤ := by
      rw [← Finset.mul_prod_erase _ _ (Nat.one_mem_divisors.2 hL0.ne'), mul_one, cyclotomic_two]
    have hX10 : (X + 1 : ℤ[X]) ≠ 0 := by
      intro h
      have := congrArg (eval 0) h
      simp at this
    have h := hmulA L hL
    rw [hplus, hsplit] at h
    exact mul_left_cancel₀ hX10 h
  have hL : Odd (Nat.lcm M N) := (hM.mul hN).of_dvd_nat (Nat.lcm_dvd_mul M N)
  have hsub : unionIdx M N ⊆ (Nat.lcm M N).divisors.erase 1 := by
    intro d hd
    simp only [unionIdx, Finset.mem_erase, Finset.mem_union, Nat.mem_divisors] at hd ⊢
    refine ⟨hd.1, ?_, Nat.lcm_ne_zero (by omega) (by omega)⟩
    rcases hd.2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h.trans (Nat.dvd_lcm_left M N)
    · exact h.trans (Nat.dvd_lcm_right M N)
  rw [hfact _ hL, joinProd, joinDefect, ← Finset.prod_sdiff hsub]
  exact mul_comm _ _
