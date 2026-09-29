-- Prove2me | solution 1 for mme_dwz_q6_022_table2_scaled_dimension_six_finite_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:01:07.455355+00:00
-- url     : https://prove2.me/submissions/ee7f2aea-7d3f-48ee-b339-152038c0540d

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_component_022_word_data
import Theorems.Thm_mme_dwz_q6_table2_022_component_power_le_dimension
import Theorems.Thm_mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
import Theorems.Thm_mme_dwz_square_componentBase_pos

open Filter Topology
open MME MME.DWZSquare
open MME.DWZTable2Component022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let D := Nat.card (Restricted022Word 6
          (table2Power022 (10366945 * m))
          (table2OuterCount022 (10366945 * m))
          (table2MiddleCount022 (10366945 * m)))
        (((componentBase tau (9 : Fin 15)) ^
            (MME.DWZTable2Counts.component 9 * m)) ^ (6 : ℕ)) *
              Real.exp (-C * Real.sqrt
                (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
          (((D : ℕ) : ℝ) ^ tau) ^ (6 : ℕ) := by
  have htau0 : 0 ≤ tau := by linarith
  let C0 : ℝ := 155520 * tau
  let C : ℝ := 6 * C0
  have hC0 : 0 ≤ C0 := by
    change 0 ≤ 155520 * tau
    positivity
  have hC : 0 ≤ C := by
    change 0 ≤ 6 * C0
    positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with m hm
  let t : ℕ := 10366945 * m
  let n : ℕ := MME.DWZTable2Counts.component 9 * m
  let D : ℕ := Nat.card (Restricted022Word 6
    (table2Power022 t) (table2OuterCount022 t)
    (table2MiddleCount022 t))
  let R : ℝ := Real.sqrt
    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
  have ht : 0 < t := by
    change 0 < 10366945 * m
    positivity
  have hn : table2Power022 t = n := by
    change 100000000 * (10366945 * m) = 1036694500000000 * m
    ring
  have hcomponent :
      componentBase tau (9 : Fin 15) ^ table2Power022 t ≤
        ((6 * ((((table2Power022 t) + 1 : ℕ) : ℝ))) ^ 3) ^ tau *
          (D : ℝ) ^ tau := by
    exact mme_dwz_q6_table2_022_component_power_le_dimension
      tau htau0 t ht
  rw [hn] at hcomponent
  have hpoly :=
    mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt tau htau0 n
  have hnle : n + 1 ≤ MME.DWZTable2Counts.scale * m + 1 := by
    change 1036694500000000 * m + 1 ≤ 10000000000000000 * m + 1
    omega
  have hsqrt :
      Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤ R := by
    change Real.sqrt (((n + 1 : ℕ) : ℝ)) ≤
      Real.sqrt (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
    apply Real.sqrt_le_sqrt
    exact_mod_cast hnle
  have hexp :
      Real.exp (C0 * Real.sqrt (((n + 1 : ℕ) : ℝ))) ≤
        Real.exp (C0 * R) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt hC0
  have hrate :
      componentBase tau (9 : Fin 15) ^ n ≤
        Real.exp (C0 * R) * (D : ℝ) ^ tau := by
    calc
      componentBase tau (9 : Fin 15) ^ n ≤
          ((6 * (((n + 1 : ℕ) : ℝ))) ^ 3) ^ tau *
            (D : ℝ) ^ tau := hcomponent
      _ ≤ Real.exp (C0 * Real.sqrt (((n + 1 : ℕ) : ℝ))) *
            (D : ℝ) ^ tau := by
        apply mul_le_mul_of_nonneg_right
        · simpa only [C0] using hpoly
        · positivity
      _ ≤ Real.exp (C0 * R) * (D : ℝ) ^ tau := by
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
  have hpow := pow_le_pow_left₀
    (pow_nonneg (mme_dwz_square_componentBase_pos tau (9 : Fin 15)).le n)
    hrate 6
  have hmul :
      (componentBase tau (9 : Fin 15) ^ n) ^ (6 : ℕ) *
          Real.exp (-C * R) ≤
        (Real.exp (C0 * R) * (D : ℝ) ^ tau) ^ (6 : ℕ) *
          Real.exp (-C * R) :=
    mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
  have hexpSix :
      (Real.exp (C0 * R)) ^ (6 : ℕ) = Real.exp (C * R) := by
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
    change 6 * (C0 * R) = (6 * C0) * R
    ring
  have hcancel :
      Real.exp (C * R) * Real.exp (-C * R) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  change (componentBase tau (9 : Fin 15) ^ n) ^ (6 : ℕ) *
      Real.exp (-C * R) ≤ ((D : ℝ) ^ tau) ^ (6 : ℕ)
  calc
    (componentBase tau (9 : Fin 15) ^ n) ^ (6 : ℕ) *
        Real.exp (-C * R) ≤
      (Real.exp (C0 * R) * (D : ℝ) ^ tau) ^ (6 : ℕ) *
        Real.exp (-C * R) := hmul
    _ = (Real.exp (C * R) * Real.exp (-C * R)) *
          ((D : ℝ) ^ tau) ^ (6 : ℕ) := by
      rw [mul_pow, hexpSix]
      ring
    _ = ((D : ℝ) ^ tau) ^ (6 : ℕ) := by rw [hcancel, one_mul]
