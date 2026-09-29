-- Prove2me | solution 2 for CyclicCubic.residue_of_root
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T17:12:28.390761+00:00
-- url     : https://prove2.me/submissions/b320fc73-437f-4a0a-9e50-819740235edf

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

open Polynomial in
theorem solution (p : ℕ) [hp : Fact p.Prime] (hp7 : p ≠ 7) (h : ∃ x : ZMod p, CyclicCubic.fval x = 0) :
    (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7p : Nat.Prime 7 := by norm_num
  have hp1 : 1 < p := hp.out.one_lt
  -- the case `p = 2`: the cubic has no root mod 2
  have hQ2' : ∀ x : ZMod 2,
      ¬ (x ^ 3 + x ^ 2 - 2 * x - 1 = 0) := by
    decide
  have hQ2 : p = 2 → ∀ x : ZMod p,
      ¬ (x ^ 3 + x ^ 2 - 2 * x - 1 = 0) := by
    intro h
    subst h
    exact hQ2'
  let K := GaloisField p 2
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p 2 (by norm_num)
  obtain ⟨x, hx⟩ := h
  simp only [CyclicCubic.fval] at hx
  by_cases hp2 : p = 2
  · exact absurd hx (hQ2 hp2 x)
  obtain ⟨xK, hxK⟩ : ∃ y : K, y = algebraMap (ZMod p) K x := ⟨_, rfl⟩
  have hQK : xK ^ 3 + xK ^ 2 - 2 * xK - 1 = 0 := by
    have h := congrArg (algebraMap (ZMod p) K) hx
    simp only [map_add, map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat] at h
    rw [hxK]
    exact h
  -- a square root of the discriminant `xK² − 4` in `GF(p²)`
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hsq : IsSquare (xK ^ 2 - 4) := by
    by_cases h0 : xK ^ 2 - 4 = 0
    · rw [h0]
      exact ⟨0, by ring⟩
    · have hd : xK ^ 2 - 4 = algebraMap (ZMod p) K (x ^ 2 - 4) := by
        rw [hxK, map_sub, map_pow, map_ofNat]
      have hne : x ^ 2 - 4 ≠ 0 := by
        intro h
        apply h0
        rw [hd, h, map_zero]
      have he : p ^ 2 / 2 = (p - 1) * ((p + 1) / 2) := by
        obtain ⟨k, hk⟩ := hp.out.odd_of_ne_two hp2
        rw [hk]
        have h1 : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
        have h2 : 2 * k + 1 - 1 = 2 * k := by omega
        have h3 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
        rw [h1, h2, h3]
        generalize 2 * k * (k + 1) = m
        omega
      rw [FiniteField.isSquare_iff hchar h0, hcardK, hd, ← map_pow, he, pow_mul,
        ZMod.pow_card_sub_one_eq_one hne, one_pow, map_one]
  obtain ⟨s, hs⟩ := hsq
  have h2K : (2 : K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : K, 2 * ζ = xK + s := ⟨(xK + s) / 2, mul_div_cancel₀ _ h2K⟩
  have hquad : ζ ^ 2 - xK * ζ + 1 = 0 := by
    have h4 : (2 : K) ^ 2 * (ζ ^ 2 - xK * ζ + 1) = 0 := by
      linear_combination (2 * ζ - xK + s) * hζdef - hs
    exact (mul_eq_zero.1 h4).resolve_left (pow_ne_zero 2 h2K)
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hquad
    norm_num at hquad
  -- `ζ` is a root of the 11th cyclotomic polynomial
  have hΦ : 1 + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
    linear_combination ζ ^ 3 * hQK - ((-1) * ζ ^ 4 + (-1) * ζ ^ 3 * xK + (-1) * ζ ^ 3
      + (-1) * ζ ^ 2 * xK ^ 2 + (-1) * ζ ^ 2 * xK + (-1) * ζ * xK + (-1) * ζ + (-1) * 1) * hquad
  have hζ7 : ζ ^ 7 = 1 := by
    linear_combination (ζ - 1) * hΦ
  have hζ1 : ζ ≠ 1 := by
    intro h1
    have h11 : (7 : K) = 0 := by
      have h := hΦ
      rw [h1] at h
      linear_combination h
    have h' : ((7 : ℕ) : K) = 0 := by exact_mod_cast h11
    rw [CharP.cast_eq_zero_iff K p] at h'
    exact hp7 ((Nat.prime_dvd_prime_iff_eq hp.out h7p).1 h')
  -- Frobenius sends `ζ` to a root of the same quadratic
  have hxp : xK ^ p = xK := by
    rw [hxK, ← map_pow, ZMod.pow_card]
  have hquadp : (ζ ^ p) ^ 2 - xK * ζ ^ p + 1 = 0 := by
    have h : (ζ ^ 2 - xK * ζ + 1) ^ p = 0 := by
      rw [hquad, zero_pow hp.out.ne_zero]
    rw [add_pow_char, sub_pow_char, mul_pow, one_pow, hxp] at h
    linear_combination h
  have hfac : (ζ ^ p - ζ) * (ζ ^ p - (xK - ζ)) = 0 := by
    linear_combination hquadp - hquad
  -- from `ζ ^ n = 1`, `ζ ^ 7 = 1`, `ζ ≠ 1` deduce `7 ∣ n`
  have hdvd : ∀ n : ℕ, ζ ^ n = 1 → 7 ∣ n := by
    intro n hn
    by_contra hnd
    have hcop : Nat.Coprime n 7 :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd h7p).2 hnd)
    have h := (pow_gcd_eq_one (a := ζ) (m := n) (n := 7)).2 ⟨hn, hζ7⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
    exact hζ1 h
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rcases mul_eq_zero.1 hfac with hA | hB
  · -- `ζ ^ p = ζ`, so `ζ ^ (p - 1) = 1`
    have hq1 : ζ * (ζ ^ q - 1) = 0 := by
      have hpq : ζ ^ p = ζ ^ (q + 1) := congrArg (ζ ^ ·) hq
      linear_combination hA - hpq
    have hzq : ζ ^ q = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hq1).resolve_left hζ0)
    have h := hdvd q hzq
    have hmod : p % 7 = 1 := by omega
    left
    rw [← ZMod.natCast_mod, hmod, Nat.cast_one]
  · -- `ζ ^ p = ζ⁻¹`, so `ζ ^ (p + 1) = 1`
    have hzp : ζ ^ (p + 1) = 1 := by
      linear_combination ζ * hB - hquad
    have h := hdvd (p + 1) hzp
    have hmod : p % 7 = 6 := by omega
    right
    rw [← ZMod.natCast_mod, hmod]
    rfl
