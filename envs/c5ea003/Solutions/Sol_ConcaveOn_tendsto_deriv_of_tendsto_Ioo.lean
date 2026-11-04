-- Prove2me | solution 1 for ConcaveOn.tendsto_deriv_of_tendsto_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-11-04T03:02:30.536289+00:00
-- url     : https://prove2.me/submissions/4206480a-d181-4c51-8381-9ffe6a84053d

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith

set_option autoImplicit false

open Filter Set
open scoped Topology

theorem solution {ι : Type*} {F : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hf : Filter.Eventually (fun n => ConcaveOn ℝ (Ioo a b) (f n)) F)
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun n ↦ f n y) F (nhds (g y)))
    (hdf : Filter.Eventually (fun n => DifferentiableAt ℝ (f n) x) F)
    (hdg : DifferentiableAt ℝ g x) :
    Tendsto (fun n ↦ deriv (f n) x) F (nhds (deriv g x)) := by
  have hslope (y : ℝ) (hy : y ∈ Ioo a b) :
      Tendsto (fun n ↦ slope (f n) x y) F (nhds (slope g x y)) := by
    simpa only [slope, smul_eq_mul, vsub_eq_sub] using
      ((hlim y hy).sub (hlim x hx)).const_mul (y - x)⁻¹
  have hnear : Filter.Eventually (fun y => y ∈ Ioo a b) (nhds x) := isOpen_Ioo.mem_nhds hx
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hright := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hgood : Filter.Eventually (fun y => y ∈ Ioo a b ∧ x < y ∧ l < slope g x y)
        (nhdsWithin x (Set.Ioi x)) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hright.eventually (lt_mem_nhds hl)] with y hy hxy hsy
      exact ⟨hy, hxy, hsy⟩
    obtain ⟨y, hy, hxy, hly⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (lt_mem_nhds hly)] with n hfn hdn hn
    exact hn.trans_le (hfn.slope_le_of_hasDerivAt hx hy hxy hdn.hasDerivAt)
  · intro u hu
    have hleft := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hgood : Filter.Eventually (fun y => y ∈ Ioo a b ∧ y < x ∧ slope g x y < u)
        (nhdsWithin x (Set.Iio x)) := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hleft.eventually (gt_mem_nhds hu)] with y hy hyx hsy
      exact ⟨hy, hyx, hsy⟩
    obtain ⟨y, hy, hyx, hyu⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (gt_mem_nhds hyu)] with n hfn hdn hn
    have hle := hfn.deriv_le_slope hy hx hyx hdn
    rw [slope_comm] at hle
    exact hle.trans_lt hn
