-- Prove2me | solution 1 for lean_workbook_plus_60316
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:14:18.984661+00:00
-- url     : https://prove2.me/submissions/cef0b404-4d81-4418-af41-ff38e7cc60dc

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set MeasureTheory

theorem geometric_band_mem_unit (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) {x : ℝ} (hx : x ∈ Ioc (q ^ (n + 1)) (q ^ n)) : x ∈ Ioc (0 : ℝ) 1 := by
  exact ⟨(pow_pos hq0 _).trans hx.1, hx.2.trans (pow_le_one₀ hq0.le hq1.le)⟩

theorem floor_logb_geometric_band (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (n : ℕ) (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    Nat.floor (Real.logb q x) = n ↔ x ∈ Ioc (q ^ (n + 1)) (q ^ n) := by
  have hlog : 0 ≤ Real.logb q x :=
    Real.logb_nonneg_of_base_lt_one hq0 hq1 hx.1 hx.2
  rw [Nat.floor_eq_iff hlog,
    Real.le_logb_iff_rpow_le_of_base_lt_one hq0 hq1 hx.1,
    show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
    Real.logb_lt_iff_lt_rpow_of_base_lt_one hq0 hq1 hx.1,
    Real.rpow_natCast, Real.rpow_natCast]
  exact and_comm

theorem odd_ceil_logb_inv_iff_floor (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 1) :
    Odd (Int.ceil (Real.logb q⁻¹ x)) ↔ Odd (Nat.floor (Real.logb q x)) := by
  have hlog : 0 ≤ Real.logb q x :=
    Real.logb_nonneg_of_base_lt_one hq0 hq1 hx.1 hx.2
  rw [Real.logb_inv_base, Int.ceil_neg, odd_neg, ← Int.natCast_floor_eq_floor hlog,
    Int.odd_coe_nat]

theorem logarithmic_odd_event_eq_bands (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    {x : ℝ | x ∈ Ioc (0 : ℝ) 1 ∧ Odd (Int.ceil (Real.logb q⁻¹ x))} =
      ⋃ m : ℕ, Ioc (q ^ (2 * m + 2)) (q ^ (2 * m + 1)) := by
  ext x
  constructor
  · rintro ⟨hx, ho⟩
    have hf := (odd_ceil_logb_inv_iff_floor q hq0 hq1 x hx).mp ho
    obtain ⟨m, hm⟩ := hf.exists_bit1
    apply mem_iUnion.mpr
    refine ⟨m, ?_⟩
    exact (floor_logb_geometric_band q hq0 hq1 (2 * m + 1) x hx).mp hm
  · intro hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp hx
    have hu := geometric_band_mem_unit q hq0 hq1 (2 * m + 1) hm
    refine ⟨hu, (odd_ceil_logb_inv_iff_floor q hq0 hq1 x hu).mpr ?_⟩
    rw [(floor_logb_geometric_band q hq0 hq1 (2 * m + 1) x hu).mpr hm]
    exact ⟨m, rfl⟩

theorem logarithmic_odd_bands_pairwise (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Pairwise (fun m n : ℕ => Disjoint
      (Ioc (q ^ (2 * m + 2)) (q ^ (2 * m + 1)))
      (Ioc (q ^ (2 * n + 2)) (q ^ (2 * n + 1)))) := by
  intro m n hmn
  apply disjoint_left.mpr
  intro x hx hy
  have hu := geometric_band_mem_unit q hq0 hq1 (2 * m + 1) hx
  have hm := (floor_logb_geometric_band q hq0 hq1 (2 * m + 1) x hu).mpr hx
  have hn := (floor_logb_geometric_band q hq0 hq1 (2 * n + 1) x hu).mpr hy
  exact hmn (by omega)

theorem geometric_odd_band_lengths_hasSum (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => q ^ (2 * m + 1) - q ^ (2 * m + 2)) (q / (1 + q)) := by
  have hq2 : |q ^ 2| < 1 := by
    rw [abs_of_nonneg (sq_nonneg q)]
    nlinarith
  have h := (hasSum_geometric_of_abs_lt_one hq2).mul_left (q * (1 - q))
  have he (m : ℕ) : q ^ (2 * m + 1) - q ^ (2 * m + 2) =
      q * (1 - q) * (q ^ 2) ^ m := by
    rw [pow_add, pow_add, pow_mul]
    ring
  have hc : q * (1 - q) * (1 - q ^ 2)⁻¹ = q / (1 + q) := by
    have hn : 1 - q ≠ 0 := by linarith
    have hp : 1 + q ≠ 0 := by linarith
    have hq : 1 - q ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  simpa only [hc] using h.congr_fun he

theorem logarithmic_odd_event_volume (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    volume {x : ℝ | x ∈ Ioc (0 : ℝ) 1 ∧ Odd (Int.ceil (Real.logb q⁻¹ x))} =
      ENNReal.ofReal (q / (1 + q)) := by
  rw [logarithmic_odd_event_eq_bands q hq0 hq1,
    measure_iUnion (logarithmic_odd_bands_pairwise q hq0 hq1) (fun _ => measurableSet_Ioc)]
  simp_rw [Real.volume_Ioc]
  have hs := geometric_odd_band_lengths_hasSum q hq0 hq1
  rw [← ENNReal.ofReal_tsum_of_nonneg, hs.tsum_eq]
  · intro m
    have hp := pow_nonneg hq0.le (2 * m + 1)
    have he : q ^ (2 * m + 2) = q ^ (2 * m + 1) * q := by
      exact pow_succ q (2 * m + 1)
    rw [he]
    exact sub_nonneg.mpr (mul_le_of_le_one_right hp hq1.le)
  · exact hs.summable

theorem logarithmic_odd_event_measurable (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    MeasurableSet {x : ℝ | x ∈ Ioc (0 : ℝ) 1 ∧ Odd (Int.ceil (Real.logb q⁻¹ x))} := by
  rw [logarithmic_odd_event_eq_bands q hq0 hq1]
  exact MeasurableSet.iUnion fun _ => measurableSet_Ioc

theorem logarithmic_odd_event_volume_base (r : ℝ) (hr : 1 < r) :
    volume {x : ℝ | x ∈ Ioc (0 : ℝ) 1 ∧ Odd (Int.ceil (Real.logb r x))} =
      ENNReal.ofReal (1 / (r + 1)) := by
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < r⁻¹ := inv_pos.mpr hr0
  have hq1 : r⁻¹ < 1 := (inv_lt_one₀ hr0).mpr hr
  have he : r⁻¹ / (1 + r⁻¹) = 1 / (r + 1) := by
    have hp : r + 1 ≠ 0 := by linarith
    field_simp
  simpa only [inv_inv, he] using logarithmic_odd_event_volume r⁻¹ hq0 hq1

theorem uniform_unit_interval_isProbabilityMeasure :
    IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one]

theorem uniform_logarithmic_odd_probability (r : ℝ) (hr : 1 < r) :
    (volume.restrict (Ioc (0 : ℝ) 1)) {x : ℝ | Odd (Int.ceil (Real.logb r x))} =
      ENNReal.ofReal (1 / (r + 1)) := by
  rw [Measure.restrict_apply' measurableSet_Ioc, inter_comm]
  exact logarithmic_odd_event_volume_base r hr

theorem uniform_logarithmic_odd_real_probability (r : ℝ) (hr : 1 < r) :
    (volume.restrict (Ioc (0 : ℝ) 1)).real {x : ℝ | Odd (Int.ceil (Real.logb r x))} =
      1 / (r + 1) := by
  rw [measureReal_def, uniform_logarithmic_odd_probability r hr, ENNReal.toReal_ofReal]
  positivity

theorem source_uniform_log4_odd_probability :
    (volume.restrict (Ioc (0 : ℝ) 1)).real {x : ℝ | Odd (Int.ceil (Real.logb 4 x))} =
      1 / 5 := by
  convert uniform_logarithmic_odd_real_probability 4 (by norm_num) using 1
  norm_num

theorem uniform_logarithmic_probability_equation (r : ℝ) (hr : 1 < r) :
    let p := (volume.restrict (Ioc (0 : ℝ) 1)).real
      {x : ℝ | Odd (Int.ceil (Real.logb r x))}
    p = 1 / r * (1 - p) := by
  dsimp only
  rw [uniform_logarithmic_odd_real_probability r hr]
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r + 1 ≠ 0 := by linarith
  field_simp
  ring

theorem solution (p : ℝ) (h₀ : p = 1 / 4 * (1 - p)) : p = 1 / 5 := by
  linarith

#print axioms geometric_band_mem_unit
#print axioms floor_logb_geometric_band
#print axioms odd_ceil_logb_inv_iff_floor
#print axioms logarithmic_odd_event_eq_bands
#print axioms logarithmic_odd_bands_pairwise
#print axioms geometric_odd_band_lengths_hasSum
#print axioms logarithmic_odd_event_volume
#print axioms logarithmic_odd_event_measurable
#print axioms logarithmic_odd_event_volume_base
#print axioms uniform_unit_interval_isProbabilityMeasure
#print axioms uniform_logarithmic_odd_probability
#print axioms uniform_logarithmic_odd_real_probability
#print axioms source_uniform_log4_odd_probability
#print axioms uniform_logarithmic_probability_equation
#print axioms solution
