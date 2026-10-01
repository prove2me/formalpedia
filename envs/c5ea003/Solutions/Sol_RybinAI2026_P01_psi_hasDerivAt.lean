-- Prove2me | solution 1 for RybinAI2026.P01.psi_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:11:57.30591+00:00
-- url     : https://prove2.me/submissions/a28335a9-9c18-4db8-9640-20a65a212479

import Mathlib
open MeasureTheory Filter Set
open scoped Topology Interval
namespace APsi
private theorem denominator_lower (t : ℝ) (ht : 0 < t) (x : ℝ) (hx : t/2 < x)
    (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) : min 1 (t/2) ≤ 1+(x-1)*s^2 := by
  have hs2 : s^2 ≤ 1 := by nlinarith [hs.1,hs.2]
  have hm1 := min_le_left (1:ℝ) (t/2)
  have hm2 := min_le_right (1:ℝ) (t/2)
  have h1 := mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hs2)
  have h2 := mul_nonneg (sub_nonneg.mpr (hm2.trans hx.le)) (sq_nonneg s)
  nlinarith

 theorem main (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..1, (1+(x-1)*s^2)⁻¹)
      (∫ s in (0 : ℝ)..1, -(s^2*(1+(t-1)*s^2)⁻¹^2)) t := by
  let m := min 1 (t/2)
  have hm : 0 < m := lt_min (by norm_num) (by linarith)
  have hden (x : ℝ) (hx : x ∈ Ioi (t/2)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      m ≤ 1+(x-1)*s^2 := denominator_lower t ht x hx s hs
  have hdpos (x : ℝ) (hx : x ∈ Ioi (t/2)) (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      0 < 1+(x-1)*s^2 := hm.trans_le (hden x hx s hs)
  have htmem : t ∈ Ioi (t/2) := by simp only [mem_Ioi]; linarith
  apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x s : ℝ => (1+(x-1)*s^2)⁻¹)
    (F' := fun x s : ℝ => -(s^2*(1+(x-1)*s^2)⁻¹^2))
    (s := Ioi (t/2)) (bound := fun _ => (m⁻¹)^2)
    (Ioi_mem_nhds htmem) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x
    exact (show Measurable (fun s : ℝ => (1+(x-1)*s^2)⁻¹) by fun_prop).aestronglyMeasurable
  · apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    apply ContinuousOn.inv₀ (by fun_prop)
    intro s hs
    exact (hdpos t htmem s hs).ne'
  · exact (show Measurable (fun s : ℝ => -(s^2*(1+(t-1)*s^2)⁻¹^2)) by fun_prop).aestronglyMeasurable
  · filter_upwards with s hs x hx
    have hs' : s ∈ Icc (0:ℝ) 1 := by
      simpa using Ioc_subset_Icc_self hs
    have hs2 : s^2 ≤ 1 := by nlinarith [hs'.1,hs'.2]
    rw [Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (sq_nonneg s),abs_of_nonneg (sq_nonneg _)]
    calc
      s^2*(1+(x-1)*s^2)⁻¹^2 ≤ 1*(m⁻¹)^2 := by
        apply mul_le_mul hs2 _ (sq_nonneg _) (by norm_num)
        gcongr
        · exact inv_nonneg.mpr (hdpos x hx s hs').le
        · exact hden x hx s hs'
      _ = (m⁻¹)^2 := by ring
  · exact intervalIntegrable_const
  · filter_upwards with s hs x hx
    have hs' : s ∈ Icc (0:ℝ) 1 := by
      simpa using Ioc_subset_Icc_self hs
    have hd : HasDerivAt (fun y : ℝ => 1+(y-1)*s^2) (s^2) x := by
      convert (((hasDerivAt_id x).sub_const 1).mul_const (s^2)).const_add 1 using 1 <;> ring
    convert hd.inv (hdpos x hx s hs').ne' using 1 <;> simp [div_eq_mul_inv,inv_pow]
end APsi

theorem solution (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..1, (1+(x-1)*s^2)⁻¹)
      (∫ s in (0 : ℝ)..1, -(s^2*(1+(t-1)*s^2)⁻¹^2)) t := APsi.main t ht
