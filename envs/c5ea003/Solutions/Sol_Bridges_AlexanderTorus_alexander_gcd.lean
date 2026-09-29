-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_gcd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T18:28:04.239986+00:00
-- url     : https://prove2.me/submissions/840f6124-529b-4a11-9349-82f1e74ee543

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII

open Bridges.AlexanderTorus Polynomial Finset in
theorem solution {M N : ℕ} (hM : Odd M) (hN : Odd N) (hMpos : 0 < M) (hNpos : 0 < N) :
    Associated (gcd (alexander M) (alexander N)) (alexander (Nat.gcd M N)) := by
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
  have hgM : Nat.gcd M N ∣ M := Nat.gcd_dvd_left M N
  have hgN : Nat.gcd M N ∣ N := Nat.gcd_dvd_right M N
  have hgodd : Odd (Nat.gcd M N) := hM.of_dvd_nat hgM
  refine associated_of_dvd_dvd ?_
    (dvd_gcd (hdvdA _ M hgM) (hdvdA _ N hgN))
  have hDM : gcd (alexander M) (alexander N) ∣ alexander M := gcd_dvd_left _ _
  have hDN : gcd (alexander M) (alexander N) ∣ alexander N := gcd_dvd_right _ _
  by_cases hgeq : Nat.gcd M N = N
  · rw [hgeq]
    exact hDN
  have hglt : Nat.gcd M N < N := lt_of_le_of_ne (Nat.le_of_dvd hNpos hgN) hgeq
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_gcd (k := N) (n := M) hglt
  obtain ⟨b, hb⟩ : ∃ b, b = M * a / N := ⟨_, rfl⟩
  have hMa : M * a = N * b + Nat.gcd M N := by
    have h := Nat.div_add_mod (M * a) N
    rw [ha, ← hb] at h
    omega
  -- parity: `a + b` is odd
  have hpar : Odd (a + b) := by
    have h1 : Even (M * a) ↔ Even (N * b + Nat.gcd M N) := by rw [hMa]
    have hMe : ¬ Even M := Nat.not_even_iff_odd.2 hM
    have hNe : ¬ Even N := Nat.not_even_iff_odd.2 hN
    have hge : ¬ Even (Nat.gcd M N) := Nat.not_even_iff_odd.2 hgodd
    simp only [Nat.even_mul, Nat.even_add] at h1
    rw [← Nat.not_even_iff_odd, Nat.even_add]
    tauto
  have hsgn : ((-1 : ℤ[X]) ^ a) = -((-1) ^ b) := by
    have h1 : ((-1 : ℤ[X]) ^ (a + b)) = -1 := hpar.neg_one_pow
    have h2 : ((-1 : ℤ[X]) ^ b) * ((-1) ^ b) = 1 := by
      rw [← mul_pow]
      norm_num
    rw [pow_add] at h1
    linear_combination ((-1 : ℤ[X]) ^ b) * h1 - ((-1 : ℤ[X]) ^ a) * h2
  have hD1 : gcd (alexander M) (alexander N) ∣ X ^ M + 1 := by
    rw [← hmulA M hM]
    exact dvd_mul_of_dvd_right hDM _
  have hD2 : gcd (alexander M) (alexander N) ∣ X ^ N + 1 := by
    rw [← hmulA N hN]
    exact dvd_mul_of_dvd_right hDN _
  have hDa : gcd (alexander M) (alexander N) ∣ X ^ (M * a) - (-1) ^ a := by
    have h := sub_dvd_pow_sub_pow (X ^ M : ℤ[X]) (-1) a
    rw [sub_neg_eq_add, ← pow_mul] at h
    exact hD1.trans h
  have hDb : gcd (alexander M) (alexander N) ∣ X ^ (N * b) - (-1) ^ b := by
    have h := sub_dvd_pow_sub_pow (X ^ N : ℤ[X]) (-1) b
    rw [sub_neg_eq_add, ← pow_mul] at h
    exact hD2.trans h
  have hDg : gcd (alexander M) (alexander N) ∣ X ^ Nat.gcd M N + 1 := by
    have key : (-1 : ℤ[X]) ^ b * (X ^ Nat.gcd M N + 1)
        = (X ^ (M * a) - (-1) ^ a) - X ^ Nat.gcd M N * (X ^ (N * b) - (-1) ^ b) := by
      rw [hMa, pow_add, hsgn]
      ring
    have h3 : gcd (alexander M) (alexander N) ∣ (-1 : ℤ[X]) ^ b * (X ^ Nat.gcd M N + 1) := by
      rw [key]
      exact dvd_sub hDa (dvd_mul_of_dvd_right hDb _)
    have hunit : IsUnit ((-1 : ℤ[X]) ^ b) := (isUnit_one.neg).pow b
    exact (hunit.dvd_mul_left).1 h3
  -- `X + 1` is prime to the gcd, since `A_M(-1) = M ≠ 0`
  have hX1 : (X + 1 : ℤ[X]) = X - C (-1) := by
    rw [map_neg, C_1, sub_neg_eq_add]
  have hirr : Irreducible (X + 1 : ℤ[X]) := by
    rw [hX1]
    exact irreducible_X_sub_C (-1)
  have hndvd : ¬ (X + 1 : ℤ[X]) ∣ alexander M := by
    intro h
    rw [hX1, dvd_iff_isRoot, halex, IsRoot, eval_finsetSum] at h
    simp at h
    omega
  have hrel : IsRelPrime (gcd (alexander M) (alexander N)) (X + 1) :=
    ((hirr.isRelPrime_iff_not_dvd).2 (fun h => hndvd (h.trans hDM))).symm
  have hDg' : gcd (alexander M) (alexander N) ∣ (X + 1) * alexander (Nat.gcd M N) := by
    rw [hmulA _ hgodd]
    exact hDg
  exact hrel.dvd_of_dvd_mul_left hDg'
