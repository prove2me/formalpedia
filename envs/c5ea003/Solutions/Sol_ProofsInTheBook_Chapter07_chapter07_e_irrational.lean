-- Prove2me | solution 1 for ProofsInTheBook.Chapter07.chapter07_e_irrational
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T14:43:33.17327+00:00
-- url     : https://prove2.me/submissions/feebf07a-3b05-42e6-a756-eaa511772e43

import Mathlib


/-!
# Chapter 7: Some irrational numbers

From "Proofs from THE BOOK":

The book proves √2, e, and π are irrational using elementary arguments.

**√p is irrational** (for any prime p): The classic proof by contradiction.
If √p = a/b with gcd(a,b) = 1, then p·b² = a², so p | a. Writing a = pc,
we get p·b² = p²c², hence b² = pc², so p | b. But gcd(a,b) = 1, contradiction.

**e is irrational**: Using e = ∑ 1/k!, if e = a/b then
n!·(e - ∑_{k=0}^n 1/k!) is an integer strictly between 0 and 1 for n = |b|+2,
a contradiction.

**π² is irrational** (hence π is irrational): Niven's proof constructs
a polynomial integral that is simultaneously a positive integer and
tends to zero.
-/

set_option maxHeartbeats 800000

namespace ProofsInTheBook.Chapter07

open scoped BigOperators

/-!
### √p is irrational for prime p

*Book proof.* Suppose √p = a/b in lowest terms. Then a² = pb², so p | a².
Since p is prime, p | a. Write a = pc. Then p²c² = pb², so pc² = b²,
giving p | b. This contradicts gcd(a,b) = 1.
-/





/-!
### e is irrational

*Book proof.* Write e = ∑_{k=0}^∞ 1/k!. If e = a/b, pick n = |b|+2 > b and consider
  n! · (e - ∑_{k=0}^n 1/k!) = ∑_{j≥0} n!/(n+1+j)!
Each term ≤ (1/(n+1))^(j+1), so the sum ≤ 1/n ≤ 1/2 < 1.
This quantity is also a positive integer (n!·e is an integer since b|n!,
and n!·∑1/k! is an integer termwise), a contradiction.
-/

private lemma exp_one_hasSum_factorial :
    HasSum (fun k : ℕ => (1 : ℝ) / (k.factorial : ℝ)) (Real.exp 1) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa [one_pow] using
    (NormedSpace.expSeries_div_hasSum_exp_of_mem_ball
      (𝕂 := ℝ) (𝔸 := ℝ) (x := (1 : ℝ))
      ((NormedSpace.expSeries_radius_eq_top ℝ ℝ).symm ▸ edist_lt_top _ _))

private lemma scaled_exp_partial_sum_is_int (n : ℕ) :
    ∃ z : ℤ,
      (n.factorial : ℝ) *
        (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)) = z := by
  classical
  refine ⟨∑ k ∈ Finset.range (n + 1), ((n.factorial / k.factorial : ℕ) : ℤ), ?_⟩
  rw [Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_natCast]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk
  have hdiv : k.factorial ∣ n.factorial := Nat.factorial_dvd_factorial hk_le
  have hkfac_ne : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnat : (n.factorial / k.factorial : ℕ) * k.factorial = n.factorial :=
    Nat.div_mul_cancel hdiv
  calc
    (n.factorial : ℝ) * (1 / (k.factorial : ℝ))
        = (n.factorial : ℝ) / (k.factorial : ℝ) := by ring
    _ = ((n.factorial / k.factorial : ℕ) : ℝ) := by
      rw [div_eq_iff hkfac_ne]; exact_mod_cast hnat.symm

private lemma factorial_tail_le_geom (n j : ℕ) (_hn : 0 < n) :
    (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ) ≤
      (1 / ((n + 1 : ℕ) : ℝ)) ^ (j + 1) := by
  have hfac_ne : ((n.factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hasc_pos_nat : 0 < (n + 1).ascFactorial (j + 1) := Nat.ascFactorial_pos n (j + 1)
  have hasc_ne : (((n + 1).ascFactorial (j + 1) : ℕ) : ℝ) ≠ 0 :=
    by exact_mod_cast ne_of_gt hasc_pos_nat
  have hpow_le_asc_nat : (n + 1) ^ (j + 1) ≤ (n + 1).ascFactorial (j + 1) :=
    Nat.pow_succ_le_ascFactorial (n + 1) (j + 1)
  have hpow_pos : 0 < (((n + 1) ^ (j + 1) : ℕ) : ℝ) :=
    by exact_mod_cast (pow_pos (Nat.succ_pos n) (j + 1))
  have hpow_le_asc : (((n + 1) ^ (j + 1) : ℕ) : ℝ) ≤
      (((n + 1).ascFactorial (j + 1) : ℕ) : ℝ) :=
    by exact_mod_cast hpow_le_asc_nat
  calc
    (n.factorial : ℝ) / ((n + 1 + j).factorial : ℝ)
        = 1 / (((n + 1).ascFactorial (j + 1) : ℕ) : ℝ) := by
          rw [show n + 1 + j = n + (j + 1) by omega]
          have h := Nat.factorial_mul_ascFactorial n (j + 1)
          rw [← h, Nat.cast_mul]; field_simp [hfac_ne, hasc_ne]
    _ ≤ 1 / (((n + 1) ^ (j + 1) : ℕ) : ℝ) :=
          one_div_le_one_div_of_le hpow_pos hpow_le_asc
    _ = (1 / ((n + 1 : ℕ) : ℝ)) ^ (j + 1) := by
          rw [Nat.cast_pow]; exact (one_div_pow _ _).symm

private lemma scaled_exp_tail_pos_lt_one (n : ℕ) (hn : 1 < n) :
    0 < (n.factorial : ℝ) *
          (Real.exp 1 - ∑ k ∈ Finset.range (n + 1), 1 / (k.factorial : ℝ)) ∧
    (n.factorial : ℝ) *
          (Real.exp 1 - ∑ k ∈ Finset.range (n + 1), 1 / (k.factorial : ℝ)) < 1 := by
  classical
  let T : ℝ := Real.exp 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)
  have hn_pos : 0 < n := by omega
  have htail : HasSum (fun j : ℕ => (1 : ℝ) / (((n + 1) + j).factorial : ℝ)) T := by
    dsimp [T]
    have h := (hasSum_nat_add_iff' (n + 1)).mpr exp_one_hasSum_factorial
    have heq : (fun j : ℕ => (1 : ℝ) / (((n + 1) + j).factorial : ℝ)) =
               (fun j : ℕ => (1 : ℝ) / ((j + (n + 1)).factorial : ℝ)) := by
      ext j; ring_nf
    rw [heq]; exact h
  have htail_eq : T = ∑' j : ℕ, (1 : ℝ) / (((n + 1) + j).factorial : ℝ) :=
    htail.tsum_eq.symm
  have hnfac_pos : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  constructor
  · have htail_pos : 0 < T := by
      rw [htail_eq]
      exact htail.summable.tsum_pos (fun j => by positivity) 0 (by positivity)
    exact mul_pos hnfac_pos htail_pos
  · let r : ℝ := (1 : ℝ) / ((n + 1 : ℕ) : ℝ)
    have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hn1R_pos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hr_nonneg : 0 ≤ r := by dsimp [r]; positivity
    have hr_lt_one : r < 1 := by
      dsimp [r]; rw [div_lt_one hn1R_pos]
      exact_mod_cast show 1 < n + 1 by omega
    have hgeo : (∑' j : ℕ, r ^ (j + 1)) = 1 / (n : ℝ) := by
      calc (∑' j : ℕ, r ^ (j + 1))
            = r * (∑' j : ℕ, r ^ j) := by simp_rw [pow_succ, mul_comm _ r]; rw [tsum_mul_left]
          _ = r * (1 - r)⁻¹ := by rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]
          _ = 1 / (n : ℝ) := by
                dsimp [r]; field_simp [hnR_pos.ne', hn1R_pos.ne']; push_cast; ring
    have hterm_le : ∀ j : ℕ,
        (n.factorial : ℝ) * ((1 : ℝ) / (((n + 1) + j).factorial : ℝ)) ≤ r ^ (j + 1) := by
      intro j; dsimp [r]; rw [mul_one_div]; exact factorial_tail_le_geom n j hn_pos
    have hsum_r_shift : Summable (fun j : ℕ => r ^ (j + 1)) := by
      simp_rw [pow_succ, mul_comm]
      exact (summable_geometric_of_lt_one hr_nonneg hr_lt_one).const_smul r
    have hfac_summable : Summable (fun j : ℕ =>
        (n.factorial : ℝ) * (1 / ((n + 1 + j).factorial : ℝ))) :=
      Summable.of_nonneg_of_le (fun j => by positivity) hterm_le hsum_r_shift
    have hfac_mul_tail : (n.factorial : ℝ) * T ≤ ∑' j : ℕ, r ^ (j + 1) := by
      rw [htail_eq, ← tsum_mul_left]
      exact Summable.tsum_le_tsum hterm_le hfac_summable hsum_r_shift
    linarith [hfac_mul_tail.trans hgeo.le,
              div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
                (by norm_num : (0:ℝ) < 2) (by exact_mod_cast hn : (2:ℝ) ≤ n)]

private lemma int_not_between_zero_and_one (x : ℝ) (hx_int : ∃ z : ℤ, x = z) :
    ¬ (0 < x ∧ x < 1) := by
  rintro ⟨hx0, hx1⟩
  obtain ⟨z, rfl⟩ := hx_int
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hx0
  have hz1 : z < 1 := by exact_mod_cast hx1
  omega



/-!
### π is irrational

*Book proof.* Niven's short proof: for π = a/b, define
  f(x) = x^n(a - bx)^n / n!
and F(x) = f(x) - f''(x) + f⁴(x) - ⋯. Then d/dx[F'sinx - Fcosx] = f(x)sinx,
so ∫₀^π f(x)sin(x) dx = F(0) + F(π) is a positive integer.
But 0 < ∫₀^π f(x)sin(x) dx < π·(πa)^n/n! → 0, contradiction for large n.
-/





end ProofsInTheBook.Chapter07

set_option maxHeartbeats 800000
open scoped BigOperators
open ProofsInTheBook.Chapter07

theorem solution : Irrational (Real.exp 1) := by
  rw [irrational_iff_ne_rational]
  intro a b hb he
  let B : ℕ := b.natAbs
  have hB_pos : B ≠ 0 := Int.natAbs_ne_zero.mpr hb
  let n : ℕ := B + 2
  have hB_le_n : B ≤ n := by dsimp [n]; omega
  have hn2 : 1 < n := by dsimp [n]; omega
  have hB_dvd_fact : B ∣ n.factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero hB_pos) hB_le_n
  have h_scaled_exp_int : ∃ z : ℤ, (n.factorial : ℝ) * Real.exp 1 = z := by
    obtain ⟨c, hc⟩ := hB_dvd_fact
    have hb_dvd_fact_int : b ∣ (n.factorial : ℤ) := by
      refine ⟨b.sign * (c : ℤ), ?_⟩
      calc (n.factorial : ℤ)
              = ((B * c : ℕ) : ℤ) := by exact_mod_cast hc
            _ = (B : ℤ) * (c : ℤ) := by norm_num
            _ = (b.natAbs : ℤ) * (c : ℤ) := by dsimp [B]
            _ = (b.sign * b) * (c : ℤ) := by rw [Int.sign_mul_self_eq_natAbs]
            _ = b * (b.sign * (c : ℤ)) := by ring
    obtain ⟨q, hq⟩ := hb_dvd_fact_int
    refine ⟨q * a, ?_⟩
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hqR : (n.factorial : ℝ) = (b : ℝ) * (q : ℝ) := by exact_mod_cast hq
    calc (n.factorial : ℝ) * Real.exp 1
            = (n.factorial : ℝ) * ((a : ℝ) / (b : ℝ)) := by rw [he]
          _ = ((b : ℝ) * (q : ℝ)) * ((a : ℝ) / (b : ℝ)) := by rw [hqR]
          _ = (q : ℝ) * (a : ℝ) := by field_simp [hbR]
          _ = ((q * a : ℤ) : ℝ) := by norm_cast
  have h_partial_int := scaled_exp_partial_sum_is_int n
  let T : ℝ := (n.factorial : ℝ) *
    (Real.exp 1 - ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ))
  have hT_int : ∃ z : ℤ, T = z := by
    obtain ⟨z₁, hz₁⟩ := h_scaled_exp_int
    obtain ⟨z₂, hz₂⟩ := h_partial_int
    exact ⟨z₁ - z₂, by dsimp [T]; rw [mul_sub, hz₁, hz₂]; push_cast; ring⟩
  have hT_between : 0 < T ∧ T < 1 := scaled_exp_tail_pos_lt_one n hn2
  exact int_not_between_zero_and_one T hT_int hT_between
