-- Prove2me | solution 1 for mme_scaled_multinomial_log_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T20:41:53.884163+00:00
-- url     : https://prove2.me/submissions/a185f97e-b6d0-49f1-8fa4-07c10db1c948

import Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field

open BigOperators MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZAmbientEntropy

theorem massEntropy_nat {C : Type*} [Fintype C] (n : C → ℕ) :
    massEntropy (fun c ↦ (n c : ℝ)) =
      ((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  simp only [massEntropy, entropy, Real.negMulLog, neg_mul,
    Finset.sum_neg_distrib, Nat.cast_sum]
  ring

theorem massEntropy_mul {C : Type*} [Fintype C] (x : C → ℝ) (m : ℝ) :
    massEntropy (fun c ↦ x c * m) = m * massEntropy x := by
  unfold massEntropy entropy
  rw [← Finset.sum_mul, Real.negMulLog_mul]
  simp only [Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

theorem fiber_massEntropy {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g) :
    (∑ g, massEntropy (fun c : {c : C // grade c = g} ↦ (n c.val : ℝ))) =
      (∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ) := by
  classical
  simp_rw [massEntropy_nat, hrow]
  rw [Finset.sum_sub_distrib,
    Fintype.sum_fiberwise grade (fun c ↦ (n c : ℝ) * Real.log (n c : ℝ))]

theorem fiber_factorial_entropy_bounds {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (n : C → ℕ) (M : G → ℕ) (S : ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, n c.val = M g)
    (hS : ∀ g, M g ≤ S) :
    ((∏ g, (M g).factorial /
      ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) ≤
        Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
          ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * ((S : ℝ) + 1)) ^ Fintype.card C *
        ((∏ g, (M g).factorial /
          ∏ c : {c : C // grade c = g}, (n c.val).factorial : ℕ) : ℝ) := by
  classical
  have hc : (∑ g, Fintype.card {c : C // grade c = g}) = Fintype.card C := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
      (Fintype.sum_fiberwise grade (fun _ ↦ (1 : ℕ)))
  have h := mme_regional_dependent_profile_entropy_bounds
    (fun g (c : {c : C // grade c = g}) ↦ n c.val) S
    (fun g ↦ (hrow g).trans_le (hS g))
  simpa only [fiber_massEntropy grade n M hrow, hc, hrow, Nat.cast_prod] using h

theorem multinomial_entropy_bounds {C : Type*} [Fintype C] (n : C → ℕ) :
    (Nat.multinomial Finset.univ n : ℝ) ≤
      Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * (((∑ c, n c : ℕ) : ℝ) + 1)) ^ Fintype.card C *
        (Nat.multinomial Finset.univ n : ℝ) := by
  classical
  have h := mme_regional_dependent_profile_entropy_bounds
    (R := Unit) (fun _ ↦ n) (∑ c, n c) (fun _ ↦ le_refl _)
  simpa only [Fintype.prod_unique, Fintype.sum_unique, massEntropy_nat,
    Nat.multinomial] using h

theorem multinomial_cast_eq_real_factorial_quotient {C : Type*} [Fintype C]
    (n : C → ℕ) :
    (Nat.multinomial Finset.univ n : ℝ) =
      (((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ) := by
  classical
  rw [Nat.multinomial, Nat.cast_div_charZero
    (Nat.prod_factorial_dvd_factorial_sum Finset.univ n), Nat.cast_prod]

theorem real_factorial_quotient_entropy_bounds {C : Type*} [Fintype C]
    (n : C → ℕ) :
    ((((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ)) ≤
      Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ∧
    Real.exp (((∑ c, n c : ℕ) : ℝ) * Real.log ((∑ c, n c : ℕ) : ℝ) -
        ∑ c, (n c : ℝ) * Real.log (n c : ℝ)) ≤
      (6 * (((∑ c, n c : ℕ) : ℝ) + 1)) ^ Fintype.card C *
        ((((∑ c, n c).factorial : ℕ) : ℝ) / ∏ c, ((n c).factorial : ℝ)) := by
  simpa only [multinomial_cast_eq_real_factorial_quotient] using
    multinomial_entropy_bounds n

theorem scaled_multinomial_log_bounds {C : Type*} [Fintype C]
    (a : C → ℕ) (m : ℕ) :
    (m : ℝ) * massEntropy (fun c ↦ (a c : ℝ)) -
        (Fintype.card C : ℝ) *
          Real.log (6 * ((((∑ c, a c) * m : ℕ) : ℝ) + 1)) ≤
      Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) ∧
    Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) ≤
      (m : ℝ) * massEntropy (fun c ↦ (a c : ℝ)) := by
  classical
  have h := multinomial_entropy_bounds (fun c ↦ a c * m)
  simp only [← massEntropy_nat] at h
  simp only [Nat.cast_mul, Nat.cast_sum, massEntropy_mul, ← Finset.sum_mul] at h
  have hpos : (0 : ℝ) < Nat.multinomial Finset.univ (fun c ↦ a c * m) := by
    exact_mod_cast Nat.multinomial_pos (s := Finset.univ) (f := fun c ↦ a c * m)
  have hbase : (0 : ℝ) < 6 * (((∑ c, (a c : ℝ)) * (m : ℝ)) + 1) := by positivity
  have hup := Real.log_le_log hpos h.1
  rw [Real.log_exp] at hup
  have hlo := Real.log_le_log (Real.exp_pos _) h.2
  rw [Real.log_exp, Real.log_mul (pow_pos hbase _).ne' hpos.ne', Real.log_pow] at hlo
  constructor
  · simp only [Nat.cast_mul, Nat.cast_sum]
    linarith
  · exact hup

end MME.DWZAmbientEntropy

open BigOperators Filter MME.RegionRate
open scoped Topology Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZAmbientEntropy

theorem log_affine_div_nat_tendsto (A : ℝ) (hA : 0 ≤ A) :
    Tendsto (fun m : ℕ ↦ Real.log (6 * (A * (m : ℝ) + 1)) / (m : ℝ))
      atTop (𝓝 0) := by
  have hconst : Tendsto (fun m : ℕ ↦ Real.log (6 * (A + 1)) / (m : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (m : ℝ) / (m : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun m : ℕ ↦
      Real.log (6 * (A + 1)) / (m : ℝ) + Real.log (m : ℝ) / (m : ℝ))
      atTop (𝓝 0) := by simpa using hconst.add hlog
  apply tendsto_const_nhds.squeeze' hupper
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    apply div_nonneg (Real.log_nonneg _) hm0
    nlinarith [mul_nonneg hA hm0]
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
    have hc : (0 : ℝ) < 6 * (A + 1) := by positivity
    have hl : Real.log (6 * (A * (m : ℝ) + 1)) ≤
        Real.log ((6 * (A + 1)) * (m : ℝ)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    rw [Real.log_mul hc.ne' hm0.ne'] at hl
    simpa only [add_div] using div_le_div_of_nonneg_right hl hm0.le

theorem scaled_multinomial_log_rate {C : Type*} [Fintype C] (a : C → ℕ) :
    Tendsto (fun m : ℕ ↦
        Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) / (m : ℝ))
      atTop (𝓝 (((∑ c, a c : ℕ) : ℝ) * Real.log ((∑ c, a c : ℕ) : ℝ) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ))) := by
  classical
  rw [← massEntropy_nat]
  have herror : Tendsto (fun m : ℕ ↦
      (Fintype.card C : ℝ) *
        Real.log (6 * (((∑ c, a c : ℕ) : ℝ) * (m : ℝ) + 1)) / (m : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (log_affine_div_nat_tendsto ((∑ c, a c : ℕ) : ℝ) (by positivity)).const_mul
        (Fintype.card C : ℝ)
  have hlower : Tendsto (fun m : ℕ ↦ massEntropy (fun c ↦ (a c : ℝ)) -
      (Fintype.card C : ℝ) *
        Real.log (6 * (((∑ c, a c : ℕ) : ℝ) * (m : ℝ) + 1)) / (m : ℝ))
      atTop (𝓝 (massEntropy (fun c ↦ (a c : ℝ)))) := by
    simpa using tendsto_const_nhds.sub herror
  apply hlower.squeeze' tendsto_const_nhds
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have h := (scaled_multinomial_log_bounds a m).1
    have hd := div_le_div_of_nonneg_right h hm0.le
    simpa only [Nat.cast_mul, sub_div, mul_div_cancel_left₀ _ hm0.ne'] using hd
  · filter_upwards [eventually_gt_atTop 0] with m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hd := div_le_div_of_nonneg_right (scaled_multinomial_log_bounds a m).2 hm0.le
    simpa only [mul_div_cancel_left₀ _ hm0.ne'] using hd

theorem scaled_fiber_factorial_log_rate {C G : Type*} [Fintype C] [Fintype G]
    (grade : C → G) (a : C → ℕ) (M : G → ℕ)
    (hrow : ∀ g, ∑ c : {c : C // grade c = g}, a c.val = M g) :
    Tendsto (fun m : ℕ ↦
      Real.log ((∏ g, (M g * m).factorial /
        ∏ c : {c : C // grade c = g}, (a c.val * m).factorial : ℕ) : ℝ) / (m : ℝ))
      atTop (𝓝 ((∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ))) := by
  classical
  have hlimits (g : G) := scaled_multinomial_log_rate
    (fun c : {c : C // grade c = g} ↦ a c.val)
  have hsum := tendsto_finset_sum Finset.univ (fun g _ ↦ hlimits g)
  have hpotential : (∑ g,
      (((∑ c : {c : C // grade c = g}, a c.val : ℕ) : ℝ) *
        Real.log ((∑ c : {c : C // grade c = g}, a c.val : ℕ) : ℝ) -
      ∑ c : {c : C // grade c = g}, (a c.val : ℝ) * Real.log (a c.val : ℝ))) =
      (∑ g, (M g : ℝ) * Real.log (M g : ℝ)) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ) := by
    simpa only [massEntropy_nat] using fiber_massEntropy grade a M hrow
  rw [hpotential] at hsum
  convert hsum using 1
  funext m
  rw [Nat.cast_prod, Real.log_prod]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    congr 2
    simp only [Nat.multinomial, ← Finset.sum_mul, hrow]
  · intro g _
    have hident : (M g * m).factorial /
        (∏ c : {c : C // grade c = g}, (a c.val * m).factorial) =
        Nat.multinomial Finset.univ (fun c : {c : C // grade c = g} ↦ a c.val * m) := by
      simp only [Nat.multinomial, ← Finset.sum_mul, hrow]
    rw [hident]
    exact_mod_cast (Nat.multinomial_pos
      (s := Finset.univ) (f := fun c : {c : C // grade c = g} ↦ a c.val * m)).ne'

end MME.DWZAmbientEntropy

open BigOperators Filter
open scoped Topology Classical

theorem solution {C : Type*} [Fintype C] (a : C → ℕ) :
    Tendsto (fun m : ℕ ↦
        Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) / (m : ℝ))
      atTop (𝓝 (((∑ c, a c : ℕ) : ℝ) * Real.log ((∑ c, a c : ℕ) : ℝ) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ))) := by
  exact MME.DWZAmbientEntropy.scaled_multinomial_log_rate a
