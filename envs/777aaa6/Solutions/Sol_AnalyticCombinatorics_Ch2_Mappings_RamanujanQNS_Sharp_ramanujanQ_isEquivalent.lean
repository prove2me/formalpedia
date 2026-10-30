-- Prove2me | solution 1 for AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp.ramanujanQ_isEquivalent
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:49:48.834238+00:00
-- url     : https://prove2.me/submissions/d15e01e1-ceba-482e-b800-ba244a921353

import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
import Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQSharp
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ramanujan's Q-function for random mappings

This file defines the finite Ramanujan Q-function from Flajolet--Sedgewick,
Chapter II.3.  The intended asymptotic is

`Q(n) ~ sqrt (pi * n / 2)`.

The full Laplace-method asymptotic is not yet present in Mathlib.  This file
records the faithful finite definition and elementary verified bounds that are
used by that proof.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

lemma sum_range_succ_cast (k : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ))) =
      (k : ℝ) * ((k : ℝ) + 1) / 2 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]
      ring

lemma sum_range_succ_cast_div (k n : ℕ) :
    (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
      ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
  rw [← Finset.sum_div, sum_range_succ_cast]

lemma ramanujanQTerm_nonneg {n k : ℕ} (hk : k ≤ n) :
    0 ≤ ramanujanQTerm n k := by
  classical
  unfold ramanujanQTerm
  refine Finset.prod_nonneg ?_
  intro j hj
  have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
  have hjn : j + 1 ≤ n := hjk.trans hk
  by_cases hn : n = 0
  · subst hn
    have : j + 1 ≤ 0 := hjn
    omega
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
  have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hnpos_nat)]
    exact_mod_cast hjn
  linarith

lemma ramanujanQTerm_factor_le_exp {n k j : ℕ} (_hk : k ≤ n) (_hj : j ∈ Finset.range k) :
    1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤
      Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
  have h := Real.add_one_le_exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ)))
  linarith

lemma ramanujanQTerm_le_exp_sum {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
  classical
  unfold ramanujanQTerm
  calc
    (∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) ≤
        ∏ j ∈ Finset.range k, Real.exp (-(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hjn : j + 1 ≤ n := hjk.trans hk
        by_cases hn : n = 0
        · subst hn
          have : j + 1 ≤ 0 := hjn
          omega
        have hnpos_nat : 0 < n := Nat.pos_of_ne_zero hn
        have hle : (((j + 1 : ℕ) : ℝ) / (n : ℝ)) ≤ 1 := by
          rw [div_le_one (by exact_mod_cast hnpos_nat)]
          exact_mod_cast hjn
        linarith
      · intro j hj
        exact ramanujanQTerm_factor_le_exp hk hj
    _ = Real.exp (∑ j ∈ Finset.range k, -(((j + 1 : ℕ) : ℝ) / (n : ℝ))) := by
      rw [Real.exp_sum]
    _ = Real.exp (-(∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [Finset.sum_neg_distrib]

lemma ramanujanQTerm_le_exp_quadratic {n k : ℕ} (hk : k ≤ n) :
    ramanujanQTerm n k ≤
      Real.exp (-(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ))) := by
  have hsum :
      (∑ j ∈ Finset.range k, (((j : ℝ) + 1) / (n : ℝ))) =
        ((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  simpa [Nat.cast_add, hsum] using ramanujanQTerm_le_exp_sum (n := n) (k := k) hk

lemma gaussianKernel_antitoneOn {n : ℕ} (hn : 0 < n) (a : ℝ) :
    AntitoneOn (gaussianKernel n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [gaussianKernel, gaussianKernel, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ (n : ℝ)⁻¹ * 2⁻¹ := by positivity
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul : ((n : ℝ)⁻¹ * 2⁻¹) * x ^ 2 ≤
      ((n : ℝ)⁻¹ * 2⁻¹) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma ramanujanQTerm_le_gaussianKernel {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ramanujanQTerm n k ≤ gaussianKernel n k := by
  have hterm := ramanujanQTerm_le_exp_quadratic (n := n) (k := k) hk
  have hquad :
      -(((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) ≤
        -((n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2) := by
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
    have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
    have hsquare : (k : ℝ) ^ 2 ≤ (k : ℝ) * ((k : ℝ) + 1) := by
      nlinarith [hk_nonneg]
    have hdiv : (n : ℝ)⁻¹ * 2⁻¹ * (k : ℝ) ^ 2 ≤
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
      field_simp [hnpos.ne']
      nlinarith
    linarith
  exact hterm.trans (Real.exp_le_exp.mpr hquad)

lemma gaussianKernel_zero (n : ℕ) : gaussianKernel n 0 = 1 := by
  simp [gaussianKernel]

lemma sum_gaussianKernel_range_le_one_add_integral {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range n, gaussianKernel n k) ≤
      1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x := by
  cases n with
  | zero => omega
  | succ m =>
      have hanti : AntitoneOn (gaussianKernel (m + 1)) (Set.Icc 0 (0 + (m : ℝ))) := by
        exact gaussianKernel_antitoneOn (n := m + 1) (by omega) (0 + (m : ℝ))
      have hsum := AntitoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := m) hanti
      calc
        (∑ k ∈ Finset.range (m + 1), gaussianKernel (m + 1) k) =
            (∑ k ∈ Finset.range m, gaussianKernel (m + 1) (k + 1)) + 1 := by
          rw [Finset.sum_range_succ']
          simp [gaussianKernel_zero]
        _ ≤ (∫ x in (0 : ℝ)..(0 + (m : ℝ)), gaussianKernel (m + 1) x) + 1 := by
          simpa using add_le_add_right hsum 1
        _ = 1 + ∫ x in (0 : ℝ)..((m + 1 - 1 : ℕ) : ℝ), gaussianKernel (m + 1) x := by
          simp [add_comm]

lemma integral_gaussianKernel_Ioc_le_Ioi {n : ℕ} (hn : 0 < n) :
    (∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
      ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
  have hb : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hint : MeasureTheory.IntegrableOn (gaussianKernel n) (Set.Ioi (0 : ℝ)) := by
    simpa [gaussianKernel] using
      (integrableOn_Ioi_exp_neg_mul_sq_iff (b := (n : ℝ)⁻¹ * 2⁻¹)).2 (by positivity)
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))] gaussianKernel n := by
    exact Eventually.of_forall fun x => (Real.exp_pos _).le
  have hsubset : Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ) ≤ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
    exact Eventually.of_forall fun x hx => hx.1
  have hset :
      (∫ x in Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ), gaussianKernel n x) ≤
        ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x :=
    MeasureTheory.setIntegral_mono_set (s := Set.Ioc (0 : ℝ) ((n - 1 : ℕ) : ℝ))
      (t := Set.Ioi (0 : ℝ)) hint hnonneg hsubset
  have hle : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by positivity
  simpa [intervalIntegral.integral_of_le hle] using hset

lemma integral_gaussianKernel_Ioi {n : ℕ} (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x) =
      Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  simpa [gaussianKernel] using integral_gaussian_Ioi (b := (n : ℝ)⁻¹ * 2⁻¹)

/--
One-sided sharp Gaussian-integral upper bound.  The right side is equal to
`1 + sqrt (π * n / 2)` for positive `n`.
-/
theorem ramanujanQ_le_one_add_gaussian_halfline {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
  unfold ramanujanQ
  calc
    (∑ k ∈ Finset.range n, ramanujanQTerm n k) ≤
        ∑ k ∈ Finset.range n, gaussianKernel n k := by
      refine Finset.sum_le_sum ?_
      intro k hk
      exact ramanujanQTerm_le_gaussianKernel hn (Nat.le_of_lt (Finset.mem_range.mp hk))
    _ ≤ 1 + ∫ x in (0 : ℝ)..((n - 1 : ℕ) : ℝ), gaussianKernel n x :=
      sum_gaussianKernel_range_le_one_add_integral hn
    _ ≤ 1 + ∫ x : ℝ in Set.Ioi (0 : ℝ), gaussianKernel n x := by
      exact add_le_add (le_refl 1) (integral_gaussianKernel_Ioc_le_Ioi hn)
    _ = 1 + Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 := by
      rw [integral_gaussianKernel_Ioi hn]

lemma gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    Real.sqrt (Real.pi / ((n : ℝ)⁻¹ * 2⁻¹)) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hnpos : (n : ℝ) ≠ 0 := by positivity
  field_simp [hnpos]

/-- Clean form of the one-sided Gaussian upper bound. -/
theorem ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two {n : ℕ} (hn : 0 < n) :
    ramanujanQ n ≤ 1 + Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  have h := ramanujanQ_le_one_add_gaussian_halfline hn
  rw [gaussian_halfline_value_eq_sqrt_pi_mul_nat_div_two hn] at h
  exact h

end
end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

/-!
# Sharp lower asymptotic for Ramanujan's Q-function

This file proves the missing lower comparison for Ramanujan's finite
`Q`-function and upgrades the previously banked upper bound to the sharp
equivalence `Q(n) ~ sqrt (pi * n / 2)`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

namespace Sharp

lemma lowerCoeff_pos {m : ℕ} (hm : 0 < m) : 0 < lowerCoeff m := by
  unfold lowerCoeff
  positivity

lemma lowerCoeff_one_le {m : ℕ} (hm : 0 < m) : 1 ≤ lowerCoeff m := by
  unfold lowerCoeff
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [one_le_div hm']
  norm_num

lemma lowerGaussian_antitoneOn {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (a : ℝ) :
    AntitoneOn (lowerGaussian m n) (Set.Icc 0 a) := by
  intro x hx y hy hxy
  rw [lowerGaussian, lowerGaussian, Real.exp_le_exp]
  have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
    exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
  have hsq : x ^ 2 ≤ y ^ 2 := (sq_le_sq₀ hx.1 hy.1).2 hxy
  have hmul :
      (lowerCoeff m / (2 * (n : ℝ))) * x ^ 2 ≤
        (lowerCoeff m / (2 * (n : ℝ))) * y ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hb_nonneg
  linarith

lemma one_sub_div_pos_of_mul_le {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hi : (m + 1) * i ≤ n) :
    0 < (1 : ℝ) - (i : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm1' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hi_real : (((m + 1 : ℕ) : ℝ) * (i : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hi
  have hle : (i : ℝ) / (n : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hn']
    field_simp [hm1'.ne']
    linarith
  have hlt : (1 / ((m + 1 : ℕ) : ℝ) : ℝ) < 1 := by
    have hm1_gt : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_lt_succ hm
    exact (div_lt_one hm1').2 hm1_gt
  linarith

lemma log_one_sub_div_ge_scaled {m n i : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hi : (m + 1) * i ≤ n) :
    -(lowerCoeff m * ((i : ℝ) / (n : ℝ))) ≤
      Real.log (1 - (i : ℝ) / (n : ℝ)) := by
  let x : ℝ := (i : ℝ) / (n : ℝ)
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm1' : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxlt : x < 1 := by
    simpa [x] using one_sub_div_pos_of_mul_le hm hn hi
  have hdenpos : 0 < 1 - x := by linarith
  have hi_real : (((m + 1 : ℕ) : ℝ) * (i : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hi
  have hx_le : x ≤ 1 / ((m + 1 : ℕ) : ℝ) := by
    dsimp [x]
    rw [div_le_iff₀ hn']
    field_simp [hm1'.ne']
    linarith
  have hone_le : 1 ≤ lowerCoeff m * (1 - x) := by
    have hden_lower : (m : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 - x := by
      have htmp : 1 - 1 / ((m + 1 : ℕ) : ℝ) ≤ 1 - x :=
        sub_le_sub_left hx_le 1
      have hident :
          1 - 1 / ((m + 1 : ℕ) : ℝ) =
            (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        field_simp [hm1'.ne']
        norm_num
      rwa [← hident]
    calc
      1 = lowerCoeff m * ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
        unfold lowerCoeff
        field_simp [hm'.ne', hm1'.ne']
      _ ≤ lowerCoeff m * (1 - x) :=
        mul_le_mul_of_nonneg_left hden_lower (lowerCoeff_pos hm).le
  have hfrac_le : x / (1 - x) ≤ lowerCoeff m * x := by
    rw [div_le_iff₀ hdenpos]
    calc
      x ≤ x * (lowerCoeff m * (1 - x)) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hone_le hx_nonneg
      _ = lowerCoeff m * x * (1 - x) := by ring
  have hbase : 1 - (1 - x)⁻¹ = -x / (1 - x) := by
    field_simp [hdenpos.ne']
    ring
  have hlog := Real.one_sub_inv_le_log_of_pos hdenpos
  rw [hbase] at hlog
  change -(lowerCoeff m * x) ≤ Real.log (1 - x)
  have hneg : -(lowerCoeff m * x) ≤ -x / (1 - x) := by
    simpa [neg_div] using neg_le_neg hfrac_le
  exact hneg.trans hlog

lemma ramanujanQTerm_ge_exp_lowerCoeff {m n k : ℕ} (hm : 0 < m)
    (hk : k < n / (m + 1)) :
    Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
        ((k : ℝ) * ((k : ℝ) + 1)))) ≤ ramanujanQTerm n k := by
  classical
  have hqpos : 0 < n / (m + 1) :=
    lt_of_le_of_lt (Nat.zero_le k) hk
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [hn0] at hqpos
  let f : ℕ → ℝ := fun j => 1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ))
  have hfactor_pos : ∀ j ∈ Finset.range k, 0 < f j := by
    intro j hj
    have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
    have hle_div : j + 1 ≤ n / (m + 1) := le_trans hjk (le_of_lt hk)
    have hmul₁ : (m + 1) * (j + 1) ≤ (m + 1) * (n / (m + 1)) :=
      Nat.mul_le_mul_left (m + 1) hle_div
    have hmul₂ : (m + 1) * (n / (m + 1)) ≤ n := by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self n (m + 1)
    exact one_sub_div_pos_of_mul_le hm hn (le_trans hmul₁ hmul₂)
  have hsumlog :
      -lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) ≤
        ∑ j ∈ Finset.range k, Real.log (f j) := by
    calc
      -lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
          ∑ j ∈ Finset.range k,
            (-(lowerCoeff m * (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
        simp [Finset.mul_sum, mul_comm]
      _ ≤ ∑ j ∈ Finset.range k, Real.log (f j) := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
        have hle_div : j + 1 ≤ n / (m + 1) := le_trans hjk (le_of_lt hk)
        have hmul₁ : (m + 1) * (j + 1) ≤ (m + 1) * (n / (m + 1)) :=
          Nat.mul_le_mul_left (m + 1) hle_div
        have hmul₂ : (m + 1) * (n / (m + 1)) ≤ n := by
          simpa [Nat.mul_comm] using Nat.div_mul_le_self n (m + 1)
        simpa [f] using
          log_one_sub_div_ge_scaled hm hn (i := j + 1) (le_trans hmul₁ hmul₂)
  have hsum_eval :
      (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ))) =
        (((k : ℝ) * ((k : ℝ) + 1) / 2) / (n : ℝ)) := by
    simpa [Nat.cast_add] using sum_range_succ_cast_div k n
  have hprod_pos : 0 < ∏ j ∈ Finset.range k, f j := by
    exact Finset.prod_pos hfactor_pos
  have hlogprod :
      Real.log (∏ j ∈ Finset.range k, f j) =
        ∑ j ∈ Finset.range k, Real.log (f j) := by
    exact Real.log_prod fun j hj => (hfactor_pos j hj).ne'
  calc
    Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
        ((k : ℝ) * ((k : ℝ) + 1)))) =
        Real.exp (-lowerCoeff m *
          (∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / (n : ℝ)))) := by
      rw [hsum_eval]
      have hn' : (n : ℝ) ≠ 0 := by positivity
      field_simp [hn']
    _ ≤ Real.exp (∑ j ∈ Finset.range k, Real.log (f j)) :=
      Real.exp_le_exp.mpr hsumlog
    _ = ∏ j ∈ Finset.range k, f j := by
      rw [← hlogprod, Real.exp_log hprod_pos]
    _ = ramanujanQTerm n k := by
      simp [ramanujanQTerm, f]

lemma lowerGaussian_succ_le_ramanujanQTerm {m n k : ℕ} (hm : 0 < m)
    (hk : k < n / (m + 1)) :
    lowerGaussian m n (k + 1 : ℕ) ≤ ramanujanQTerm n k := by
  have hqpos : 0 < n / (m + 1) :=
    lt_of_le_of_lt (Nat.zero_le k) hk
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    simp [hn0] at hqpos
  have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
    exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
  have hsq :
      (k : ℝ) * ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith
  have hexp :
      lowerGaussian m n (k + 1 : ℕ) ≤
        Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) *
          ((k : ℝ) * ((k : ℝ) + 1)))) := by
    rw [lowerGaussian, Real.exp_le_exp]
    have hmul :
        (lowerCoeff m / (2 * (n : ℝ))) * ((k : ℝ) * ((k : ℝ) + 1)) ≤
          (lowerCoeff m / (2 * (n : ℝ))) * (((k : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hb_nonneg
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by norm_num
    rw [hcast]
    linarith
  exact hexp.trans (ramanujanQTerm_ge_exp_lowerCoeff hm hk)

lemma lowerGaussian_integrableOn_Ioi {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (c : ℝ) :
    IntegrableOn (lowerGaussian m n) (Set.Ioi c) := by
  have hb : 0 < lowerCoeff m / (2 * (n : ℝ)) := by
    exact div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
  simpa [lowerGaussian] using
    (integrable_exp_neg_mul_sq hb).integrableOn (s := Set.Ioi c)

lemma lowerGaussian_integral_Ioi {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) =
      Real.sqrt (Real.pi / (lowerCoeff m / (2 * (n : ℝ)))) / 2 := by
  simpa [lowerGaussian] using
    integral_gaussian_Ioi (b := lowerCoeff m / (2 * (n : ℝ)))

lemma lowerGaussian_halfline_value {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Real.sqrt (Real.pi / (lowerCoeff m / (2 * (n : ℝ)))) / 2 =
      Real.sqrt (Real.pi * (n : ℝ) / 2) *
        Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
  apply (sq_eq_sq₀ (by positivity) (by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  have hleft_nonneg : 0 ≤ Real.pi / (lowerCoeff m / (2 * (n : ℝ))) := by
    have hb : 0 < lowerCoeff m / (2 * (n : ℝ)) :=
      div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
    exact div_nonneg Real.pi_pos.le hb.le
  have hright₁ : 0 ≤ Real.pi * (n : ℝ) / 2 := by positivity
  have hright₂ : 0 ≤ (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by positivity
  rw [div_pow, mul_pow, Real.sq_sqrt hleft_nonneg, Real.sq_sqrt hright₁,
    Real.sq_sqrt hright₂]
  unfold lowerCoeff
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hm1' : (((m + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hm', hn', hm1']

lemma lowerGaussian_integral_zero_one_le_one {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..(1 : ℝ), lowerGaussian m n x) ≤ 1 := by
  have hle : ∀ x ∈ Set.Icc (0 : ℝ) 1, lowerGaussian m n x ≤ (1 : ℝ) := by
    intro x hx
    rw [lowerGaussian, ← Real.exp_zero, Real.exp_le_exp]
    have hb_nonneg : 0 ≤ lowerCoeff m / (2 * (n : ℝ)) := by
      exact (div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))).le
    have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith [mul_nonneg hb_nonneg hx2]
  have hmono := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    ((by unfold lowerGaussian; fun_prop : Continuous (lowerGaussian m n)).intervalIntegrable 0 1)
    (intervalIntegral.intervalIntegrable_const (a := (0 : ℝ)) (b := 1) (c := (1 : ℝ)))
    hle
  simpa using hmono

lemma lowerGaussian_tail_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {K : ℝ}
    (hK : 0 < K) :
    (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K) := by
  let b : ℝ := lowerCoeff m / (2 * (n : ℝ))
  have hb : 0 < b := by
    dsimp [b]
    exact div_pos (lowerCoeff_pos hm) (by positivity : (0 : ℝ) < 2 * (n : ℝ))
  have hbK : 0 < b * K := mul_pos hb hK
  have hgauss_int : IntegrableOn (lowerGaussian m n) (Set.Ioi K) :=
    lowerGaussian_integrableOn_Ioi hm hn K
  have hlin_int : IntegrableOn (fun x : ℝ => Real.exp (-(b * K) * x)) (Set.Ioi K) := by
    exact integrableOn_exp_mul_Ioi (a := -(b * K)) (by linarith) K
  have hmono :
      (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
        ∫ x : ℝ in Set.Ioi K, Real.exp (-(b * K) * x) := by
    refine setIntegral_mono_on hgauss_int hlin_int measurableSet_Ioi ?_
    intro x hx
    have hxK : K ≤ x := le_of_lt hx
    have hx_nonneg : 0 ≤ x := le_trans hK.le hxK
    rw [lowerGaussian, Real.exp_le_exp]
    dsimp [b]
    have hsq : K * x ≤ x ^ 2 := by
      nlinarith
    have hmul : b * (K * x) ≤ b * x ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hb.le
    nlinarith
  calc
    (∫ x : ℝ in Set.Ioi K, lowerGaussian m n x) ≤
        ∫ x : ℝ in Set.Ioi K, Real.exp (-(b * K) * x) := hmono
    _ = Real.exp (-(b * K) * K) / (b * K) := by
      have h := integral_exp_mul_Ioi (a := -(b * K)) (by linarith : -(b * K) < 0) K
      rw [h]
      field_simp [hbK.ne']
    _ ≤ 1 / (b * K) := by
      have hexp : Real.exp (-(b * K) * K) ≤ 1 := by
        rw [← Real.exp_zero, Real.exp_le_exp]
        nlinarith
      exact div_le_div_of_nonneg_right hexp hbK.le

lemma lowerGaussian_tail_le_linear_head {m n : ℕ} (hm : 0 < m) (hn : m + 1 ≤ n) :
    (∫ x : ℝ in Set.Ioi (1 + (((n / (m + 1) : ℕ) : ℝ))), lowerGaussian m n x) ≤
      2 * ((m + 1 : ℕ) : ℝ) := by
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  let K : ℝ := 1 + ((n / (m + 1) : ℕ) : ℝ)
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have htail := lowerGaussian_tail_le hm hnpos (K := K) hKpos
  have hdivlt_nat : n < (n / (m + 1) + 1) * (m + 1) := by
    have hlt : n / (m + 1) < n / (m + 1) + 1 := Nat.lt_succ_self _
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos m)).mp hlt
  have hdivle_real : (n : ℝ) / K ≤ ((m + 1 : ℕ) : ℝ) := by
    have hlt_real :
        (n : ℝ) < (((n / (m + 1) + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hdivlt_nat
    have hK_eq : K = ((n / (m + 1) + 1 : ℕ) : ℝ) := by
      dsimp [K]
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hK_eq]
    have hKpos' : 0 < (((n / (m + 1) + 1 : ℕ) : ℝ)) := by positivity
    rw [div_le_iff₀ hKpos']
    exact le_of_lt (by simpa [mul_comm] using hlt_real)
  have hcoeff_ge : 1 ≤ lowerCoeff m := lowerCoeff_one_le hm
  have hmain :
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K) ≤
        2 * ((m + 1 : ℕ) : ℝ) := by
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hKreal : 0 < K := hKpos
    have hcoeff_pos : 0 < lowerCoeff m := lowerCoeff_pos hm
    calc
      1 / ((lowerCoeff m / (2 * (n : ℝ))) * K)
          = (2 * (n : ℝ)) / (lowerCoeff m * K) := by
        field_simp [hnreal.ne', hKreal.ne', hcoeff_pos.ne']
      _ ≤ (2 * (n : ℝ)) / K := by
        have hden_le : K ≤ lowerCoeff m * K := by
          simpa using mul_le_mul_of_nonneg_right hcoeff_ge hKreal.le
        exact div_le_div_of_nonneg_left (by positivity) hKreal hden_le
      _ = 2 * ((n : ℝ) / K) := by ring
      _ ≤ 2 * ((m + 1 : ℕ) : ℝ) := by
        nlinarith
  exact htail.trans hmain

theorem ramanujanQ_lower_fixed (m n : ℕ) (hm : 0 < m) (hn : m + 1 ≤ n) :
    Real.sqrt (Real.pi * (n : ℝ) / 2) *
        Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) -
        (1 + 2 * ((m + 1 : ℕ) : ℝ)) ≤ ramanujanQ n := by
  classical
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  let K : ℕ := n / (m + 1)
  have hK_le_n : K ≤ n := Nat.div_le_self n (m + 1)
  have hsubset : Finset.range K ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hK_le_n)
  have hQ_head :
      (∑ k ∈ Finset.range K, ramanujanQTerm n k) ≤ ramanujanQ n := by
    unfold ramanujanQ
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro k hk _hnot
    exact ramanujanQTerm_nonneg (Nat.le_of_lt (Finset.mem_range.mp hk))
  have hterm :
      (∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ)) ≤
        ∑ k ∈ Finset.range K, ramanujanQTerm n k := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact lowerGaussian_succ_le_ramanujanQTerm hm (Finset.mem_range.mp hk)
  have hanti :
      AntitoneOn (lowerGaussian m n)
        (Set.Icc (1 : ℝ) (1 + (K : ℝ))) := by
    exact (lowerGaussian_antitoneOn hm hnpos (1 + (K : ℝ))).mono
      (by
        intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩)
  have hint_le_sum :
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤
        ∑ k ∈ Finset.range K, lowerGaussian m n (1 + k) :=
    AntitoneOn.integral_le_sum hanti
  have hsum_cast :
      (∑ k ∈ Finset.range K, lowerGaussian m n (1 + k)) =
        ∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro k hk
    congr 1
    simp [Nat.cast_add, add_comm]
  have hintegral_head :
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤ ramanujanQ n := by
    calc
      (∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x) ≤
          ∑ k ∈ Finset.range K, lowerGaussian m n (1 + k) := hint_le_sum
      _ = ∑ k ∈ Finset.range K, lowerGaussian m n (k + 1 : ℕ) := hsum_cast
      _ ≤ ∑ k ∈ Finset.range K, ramanujanQTerm n k := hterm
      _ ≤ ramanujanQ n := hQ_head
  have htail := lowerGaussian_tail_le_linear_head hm hn
  have h01 := lowerGaussian_integral_zero_one_le_one hm hnpos
  have hint0 := lowerGaussian_integrableOn_Ioi hm hnpos (0 : ℝ)
  have hint1 := lowerGaussian_integrableOn_Ioi hm hnpos (1 : ℝ)
  have hintK := lowerGaussian_integrableOn_Ioi hm hnpos (1 + (K : ℝ))
  have h01eq :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) -
        (∫ x : ℝ in Set.Ioi (1 : ℝ), lowerGaussian m n x) =
          ∫ x in (0 : ℝ)..(1 : ℝ), lowerGaussian m n x :=
    (eq_sub_of_add_eq (intervalIntegral.integral_interval_add_Ioi hint0 hint1)).symm
  have h1Keq :
      (∫ x : ℝ in Set.Ioi (1 : ℝ), lowerGaussian m n x) -
        (∫ x : ℝ in Set.Ioi (1 + (K : ℝ)), lowerGaussian m n x) =
          ∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x :=
    (eq_sub_of_add_eq (intervalIntegral.integral_interval_add_Ioi hint1 hintK)).symm
  have hhalf :
      (∫ x : ℝ in Set.Ioi (0 : ℝ), lowerGaussian m n x) =
        Real.sqrt (Real.pi * (n : ℝ) / 2) *
          Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    rw [lowerGaussian_integral_Ioi hm hnpos, lowerGaussian_halfline_value hm hnpos]
  have hdecomp :
      Real.sqrt (Real.pi * (n : ℝ) / 2) *
          Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ)) -
          (1 + 2 * ((m + 1 : ℕ) : ℝ)) ≤
        ∫ x in (1 : ℝ)..(1 + (K : ℝ)), lowerGaussian m n x := by
    rw [← hhalf]
    linarith
  exact hdecomp.trans hintegral_head

lemma tendsto_sqrt_nat_div_nat_succ :
    Tendsto (fun m : ℕ => Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).sqrt
  simpa [Nat.cast_add, Real.sqrt_one] using h

lemma tendsto_sqrt_pi_mul_nat_div_two_atTop :
    Tendsto (fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2)) atTop atTop := by
  have hlin :
      Tendsto (fun n : ℕ => (Real.pi / 2) * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop
  refine Real.tendsto_sqrt_atTop.comp (hlin.congr' ?_)
  exact Eventually.of_forall fun n => by ring

lemma eventually_ratio_le_of_gt_one {a : ℝ} (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop,
      ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2) < a := by
  let g : ℕ → ℝ := fun n => Real.sqrt (Real.pi * (n : ℝ) / 2)
  have hg : Tendsto g atTop atTop := tendsto_sqrt_pi_mul_nat_div_two_atTop
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) / g n < a - 1 :=
    (Filter.Tendsto.const_div_atTop hg (1 : ℝ)).eventually
      (gt_mem_nhds (sub_pos.mpr ha))
  filter_upwards [hsmall, eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hsmall hn
  have hnpos : 0 < n := by omega
  have gpos : 0 < g n := by
    dsimp [g]
    positivity
  have hQ := ramanujanQ_le_one_add_sqrt_pi_mul_nat_div_two hnpos
  have hratio :
      ramanujanQ n / g n ≤ 1 + 1 / g n := by
    calc
      ramanujanQ n / g n ≤ (1 + g n) / g n :=
        div_le_div_of_nonneg_right hQ gpos.le
      _ = 1 + 1 / g n := by
        field_simp [gpos.ne']
        ring
  linarith

lemma eventually_ratio_gt_of_lt_one {a : ℝ} (ha : a < 1) :
    ∀ᶠ n : ℕ in atTop,
      a < ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2) := by
  let s : ℕ → ℝ := fun m => Real.sqrt ((m : ℝ) / ((m + 1 : ℕ) : ℝ))
  have hs_tendsto : Tendsto s atTop (𝓝 1) := tendsto_sqrt_nat_div_nat_succ
  have hs_event : ∀ᶠ m : ℕ in atTop, a < s m :=
    (tendsto_order.mp hs_tendsto).1 a ha
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hs_event
  let m : ℕ := max 1 m₀
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hma : a < s m := hm₀ m (by
    dsimp [m]
    exact le_max_right 1 m₀)
  let g : ℕ → ℝ := fun n => Real.sqrt (Real.pi * (n : ℝ) / 2)
  have hg : Tendsto g atTop atTop := tendsto_sqrt_pi_mul_nat_div_two_atTop
  let C : ℝ := 1 + 2 * ((m + 1 : ℕ) : ℝ)
  have hgap : 0 < s m - a := sub_pos.mpr hma
  have hsmall :
      ∀ᶠ n : ℕ in atTop, C / g n < s m - a :=
    (Filter.Tendsto.const_div_atTop hg C).eventually (gt_mem_nhds hgap)
  filter_upwards [hsmall, eventually_atTop.2 ⟨m + 1, fun n hn => hn⟩] with n hsmall hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos m) hn
  have gpos : 0 < g n := by
    dsimp [g]
    positivity
  have hlower := ramanujanQ_lower_fixed m n hm hn
  have hratio_lower :
      s m - C / g n ≤ ramanujanQ n / g n := by
    calc
      s m - C / g n =
          (g n * s m - C) / g n := by
        field_simp [gpos.ne']
      _ ≤ ramanujanQ n / g n :=
        div_le_div_of_nonneg_right hlower gpos.le
  linarith

theorem ramanujanQ_tendsto_ratio_one :
    Tendsto
      (fun n : ℕ => ramanujanQ n / Real.sqrt (Real.pi * (n : ℝ) / 2))
      atTop (𝓝 1) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    exact eventually_ratio_gt_of_lt_one ha
  · intro a ha
    exact eventually_ratio_le_of_gt_one ha

end Sharp
end
end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

open AnalyticCombinatorics AnalyticCombinatorics.Ch2 AnalyticCombinatorics.Ch2.Mappings AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS.Sharp
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
theorem solution :
    (fun n : ℕ => ramanujanQ n) ~[atTop]
      (fun n : ℕ => Real.sqrt (Real.pi * (n : ℝ) / 2)) := by
  exact Asymptotics.isEquivalent_of_tendsto_one ramanujanQ_tendsto_ratio_one
