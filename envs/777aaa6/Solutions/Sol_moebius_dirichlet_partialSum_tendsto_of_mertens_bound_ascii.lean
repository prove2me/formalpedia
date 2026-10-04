-- Prove2me | solution 1 for moebius_dirichlet_partialSum_tendsto_of_mertens_bound_ascii
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-03T18:46:49.92527+00:00
-- url     : https://prove2.me/submissions/7e514934-f691-46e0-9767-3af91093aff0

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.Complex.Asymptotics

set_option autoImplicit false

open Finset Filter MeasureTheory Topology Asymptotics

theorem solution
    (sigma : Real) (hsigma : 1 / 2 < sigma)
    (hM : forall epsilon : Real, 0 < epsilon ->
      Asymptotics.IsBigO Filter.atTop
        (fun N : Nat => Finset.sum (Finset.Icc 1 N)
          (fun n => (ArithmeticFunction.moebius n : Complex)))
        (fun N : Nat => (N : Real) ^ (1 / 2 + epsilon))) :
    Exists fun L : Real => Filter.Tendsto
      (fun N : Nat => Finset.sum (Finset.Icc 1 N)
        (fun n => (ArithmeticFunction.moebius n : Real) * (n : Real) ^ (-sigma)))
      Filter.atTop (nhds L) := by
  let r : ℝ := 1 / 2 + (sigma - 1 / 2) / 2
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hrs : r < sigma := by dsimp [r]; linarith
  let c : ℕ → ℝ := fun n => (ArithmeticFunction.moebius n : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hsum (N : ℕ) : ∑ k ∈ Icc 0 N, c k = ∑ k ∈ Icc 1 N, c k := by
    rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc]
    simp
  have hO : (fun N => ∑ k ∈ Icc 0 N, c k) =O[atTop] fun N => (N : ℝ) ^ r := by
    have h := hM ((sigma - 1 / 2) / 2) (by linarith)
    have h' : (fun N => ((∑ k ∈ Icc 1 N, c k : ℝ) : ℂ)) =O[atTop]
        fun N => (N : ℝ) ^ r := by
      simpa [c, r, Complex.ofReal_sum] using h
    simpa only [hsum] using (Complex.isBigO_ofReal_left.mp h')
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-sigma) * ∑ k ∈ Icc 0 N, c k)
      atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(sigma - r))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (sub_pos.mpr hrs)).comp tendsto_natCast_atTop_atTop
    exact (IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow (-sigma) r (-(sigma - r))
      (isBigO_refl _ _) hO (by linarith)).trans_tendsto hp
  have hfloor : (fun t : ℝ => ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ r :=
    (hO.comp_tendsto tendsto_nat_floor_atTop).trans
      (isEquivalent_nat_floor.isBigO.rpow hr (eventually_ge_atTop 0))
  have hdom : (fun t : ℝ => deriv (fun x : ℝ => x ^ (-sigma)) t *
      ∑ k ∈ Icc 0 ⌊t⌋₊, c k) =O[atTop] fun t => t ^ (-sigma - 1 + r) :=
    IsBigO.mul_atTop_rpow_of_isBigO_rpow (-sigma - 1) r (-sigma - 1 + r)
      (isBigO_deriv_rpow_const_atTop (-sigma)) hfloor le_rfl
  have hint : LocallyIntegrableOn (deriv (fun x : ℝ => x ^ (-sigma))) (Set.Ici 1) := by
    rw [Real.deriv_rpow_const']
    apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ici
    exact continuousOn_const.mul (fun t ht =>
      (Real.continuousAt_rpow_const _ _ (Or.inl (zero_lt_one.trans_le ht).ne')).continuousWithinAt)
  have hconv := tendsto_sum_mul_atTop_nhds_one_sub_integral₀ c hc
    (f := fun x : ℝ => x ^ (-sigma))
    (fun t ht => Real.differentiableAt_rpow_const_of_ne _ (zero_lt_one.trans_le ht).ne')
    hint hlim hdom (integrableAtFilter_rpow_atTop_iff.mpr (by linarith : -sigma - 1 + r < -1))
  refine ⟨_, hconv.congr (fun N => ?_)⟩
  rw [← insert_Icc_add_one_left_eq_Icc N.zero_le, sum_insert (by simp), hc, mul_zero, zero_add]
  simp only [zero_add]
  exact sum_congr rfl fun n _ => mul_comm _ _
