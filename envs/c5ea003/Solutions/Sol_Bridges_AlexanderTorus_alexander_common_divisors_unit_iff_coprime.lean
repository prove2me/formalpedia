-- Prove2me | solution 1 for Bridges.AlexanderTorus.alexander_common_divisors_unit_iff_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:14:54.040814+00:00
-- url     : https://prove2.me/submissions/591c1ec8-35c9-4f24-a384-c5ecfff97f2c

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridge

open Bridges.AlexanderTorus Polynomial Finset in
theorem solution {M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hM1 : 1 < M) (hN1 : 1 < N) :
    (∀ f : ℤ[X], f ∣ alexander M → f ∣ alexander N → IsUnit f) ↔ Nat.Coprime M N := by
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
  constructor
  · -- a nontrivial `gcd` gives the non-unit common factor `alexander (gcd M N)`
    intro h
    by_contra hcop
    have hgpos : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left _ (by omega)
    have hd1 : 1 < Nat.gcd M N := by
      have : Nat.gcd M N ≠ 1 := hcop
      omega
    have hdvd : ∀ K, Nat.gcd M N ∣ K → alexander (Nat.gcd M N) ∣ alexander K := by
      rintro K ⟨q, rfl⟩
      rw [halex, halex, hprod]
      exact dvd_mul_right _ _
    have hunit := h _ (hdvd M (Nat.gcd_dvd_left M N)) (hdvd N (Nat.gcd_dvd_right M N))
    have hdodd : Odd (Nat.gcd M N) := hM.of_dvd_nat (Nat.gcd_dvd_left M N)
    have hev := hunit.map (Polynomial.evalRingHom (2 : ℤ))
    rw [Int.isUnit_iff] at hev
    have h3 : 3 * (Polynomial.evalRingHom (2 : ℤ)) (alexander (Nat.gcd M N))
        = 1 + 2 ^ Nat.gcd M N := by
      rw [halex, Polynomial.coe_evalRingHom, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_X]
      have h := mul_neg_geom_sum (-2 : ℤ) (Nat.gcd M N)
      rw [hdodd.neg_pow] at h
      linarith
    have h8 : (8 : ℤ) ≤ 2 ^ Nat.gcd M N := by
      have h3le : 3 ≤ Nat.gcd M N := by
        obtain ⟨k, hk⟩ := hdodd
        omega
      calc (8 : ℤ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ Nat.gcd M N := pow_le_pow_right₀ (by norm_num) h3le
    rcases hev with h1 | h1 <;> rw [h1] at h3 <;> linarith
  · -- for coprime `M, N` a common factor has no complex root, hence is a unit
    intro hcop f hfM hfN
    by_cases hdeg : f.natDegree = 0
    · have hf : f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      obtain ⟨g, hg⟩ := hfM
      have h0 : (alexander M).coeff 0 = 1 := by
        rw [Polynomial.coeff_zero_eq_eval_zero, halex, Polynomial.eval_finsetSum,
          Finset.sum_eq_single 0]
        · simp
        · intro i _ hi
          simp [zero_pow hi]
        · intro h
          exact absurd (Finset.mem_range.2 (by omega)) h
      have hc : f.coeff 0 * g.coeff 0 = 1 := by
        rw [← h0, hg, hf, Polynomial.coeff_C_mul]
        simp
      rw [hf]
      exact Polynomial.isUnit_C.2 (isUnit_iff_exists_inv.2 ⟨_, hc⟩)
    · exfalso
      have hdegC : 0 < (f.map (Int.castRingHom ℂ)).degree := by
        rw [Polynomial.degree_map_eq_of_injective (RingHom.injective_int _)]
        exact Polynomial.natDegree_pos_iff_degree_pos.1 (Nat.pos_of_ne_zero hdeg)
      obtain ⟨ζ, hζ⟩ := Complex.exists_root hdegC
      -- a root of `f` is a root of every Alexander polynomial `f` divides
      have hsum : ∀ K, f ∣ alexander K → ∑ i ∈ range K, (-ζ) ^ i = 0 := by
        intro K hfK
        obtain ⟨g, hg⟩ := hfK
        have hev : (alexander K).eval₂ (Int.castRingHom ℂ) ζ = 0 := by
          rw [hg, Polynomial.eval₂_mul, ← Polynomial.eval_map, hζ.eq_zero, zero_mul]
        rw [halex, Polynomial.eval₂_finsetSum] at hev
        simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_neg, Polynomial.eval₂_X,
          eq_intCast, Int.cast_one] using hev
      have hpow : ∀ K, f ∣ alexander K → Odd K → ζ ^ K = -1 := by
        intro K hfK hK
        have h := mul_neg_geom_sum (-ζ) K
        rw [hsum K hfK, mul_zero, hK.neg_pow] at h
        linear_combination (-1 : ℂ) * h
      have hζM := hpow M hfM hM
      have hζN := hpow N hfN hN
      have hζ0 : ζ ≠ 0 := by
        rintro rfl
        rw [zero_pow (by omega)] at hζM
        norm_num at hζM
      obtain ⟨a, b, hab⟩ := Nat.Coprime.isCoprime hcop
      have hζ1 : ζ = (-1) ^ a * (-1) ^ b := by
        calc ζ = ζ ^ (1 : ℤ) := (zpow_one ζ).symm
          _ = ζ ^ (a * (M : ℤ) + b * (N : ℤ)) := by rw [hab]
          _ = (ζ ^ M) ^ a * (ζ ^ N) ^ b := by
              rw [zpow_add₀ hζ0, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast,
                zpow_natCast]
          _ = (-1) ^ a * (-1) ^ b := by rw [hζM, hζN]
      have hsq : ∀ c : ℤ, ((-1 : ℂ) ^ c) * ((-1) ^ c) = 1 := by
        intro c
        rw [← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]
        norm_num
      have hζζ : ζ * ζ = 1 := by
        rw [hζ1]
        calc (-1 : ℂ) ^ a * (-1) ^ b * ((-1) ^ a * (-1) ^ b)
            = ((-1) ^ a * (-1) ^ a) * ((-1) ^ b * (-1) ^ b) := by ring
          _ = 1 := by rw [hsq, hsq, one_mul]
      rcases mul_self_eq_one_iff.1 hζζ with h1 | h1
      · rw [h1, one_pow] at hζM
        norm_num at hζM
      · have h := hsum M hfM
        rw [h1, neg_neg] at h
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h
        have : (M : ℂ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
        exact this h
