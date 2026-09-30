-- Prove2me | solution 1 for KeplerMission.nonlinear_8055810915_valid
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-30T00:47:10.283078+00:00
-- url     : https://prove2.me/submissions/18553040-327e-4e6e-ad6f-d880d171d81c

import Definitions.Def_Kepler_NonlinearCatalogModel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 1000000

open KeplerMission.Nonlinear

namespace KeplerWazldcdProof

-- Direct source inequality 8055810915 (WAZLDCD), pinned Flyspeck ineq.hl:1634–1648.
-- Hales et al. (2017), Section 5, PDF p. 12, equation (2), and Section 6, pp. 16–17.
-- The rational enclosures below use Mathlib trigonometric bounds and double angles.
private theorem fixed_bounds :
    Real.sin (273402 / 1000000 : ℝ) ≤ 27001 / 100000 ∧
    96285 / 100000 ≤ Real.cos (273402 / 1000000 : ℝ) := by
  let a : ℝ := 136701 / 4000000
  have ha : 0 ≤ a := by norm_num [a]
  have ha1 : |a| ≤ 1 := by norm_num [a]
  have hs := (abs_le.mp (Real.sin_bound ha1)).2
  have hc := (abs_le.mp (Real.cos_bound ha1)).2
  have hc' : 1 - a ^ 2 / 2 ≤ Real.cos a := Real.one_sub_sq_div_two_le_cos
  rw [abs_of_nonneg ha] at hs hc
  have s0 : Real.sin a ≤ 34168669 / 1000000000 := by norm_num [a] at hs ⊢; linarith
  have c0u : Real.cos a ≤ 999416098 / 1000000000 := by norm_num [a] at hc ⊢; linarith
  have c0l : 999416026 / 1000000000 ≤ Real.cos a := by norm_num [a] at hc' ⊢; linarith
  have s0p : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi ha
    (by norm_num [a]; linarith [Real.pi_gt_d6])
  have s1 : Real.sin (2 * a) ≤ 68297436 / 1000000000 := by
    rw [Real.sin_two_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr s0) (sub_nonneg.mpr c0u)]
  have c1u : Real.cos (2 * a) ≤ 997665075 / 1000000000 := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos a - 999416098 / 1000000000)]
  have c1l : 997664786 / 1000000000 ≤ Real.cos (2 * a) := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos a - 999416026 / 1000000000)]
  have s1p : 0 ≤ Real.sin (2 * a) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by norm_num [a]; linarith [Real.pi_gt_d6])
  have s2 : Real.sin (2 * (2 * a)) ≤ 136275934 / 1000000000 := by
    rw [Real.sin_two_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr s1) (sub_nonneg.mpr c1u)]
  have c2u : Real.cos (2 * (2 * a)) ≤ 990671205 / 1000000000 := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (2 * a) - 997665075 / 1000000000)]
  have c2l : 990670050 / 1000000000 ≤ Real.cos (2 * (2 * a)) := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (2 * a) - 997664786 / 1000000000)]
  have s2p : 0 ≤ Real.sin (2 * (2 * a)) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by positivity) (by norm_num [a]; linarith [Real.pi_gt_d6])
  have s3 : Real.sin (2 * (2 * (2 * a))) ≤ 27001 / 100000 := by
    rw [Real.sin_two_mul]
    nlinarith [mul_nonneg (sub_nonneg.mpr s2) (sub_nonneg.mpr c2u)]
  have c3l : 96285 / 100000 ≤ Real.cos (2 * (2 * (2 * a))) := by
    rw [Real.cos_two_mul]
    nlinarith [sq_nonneg (Real.cos (2 * (2 * a)) - 990670050 / 1000000000)]
  convert And.intro s3 c3l using 1 <;> norm_num [a]

private theorem delta_bounds :
    Real.sin (797 / 1000 - Real.pi / 6) ≤ 27001 / 100000 ∧
    96285 / 100000 ≤ Real.cos (797 / 1000 - Real.pi / 6) := by
  have h0 : 0 ≤ 797 / 1000 - Real.pi / 6 := by linarith [Real.pi_lt_d6]
  have hu : 797 / 1000 - Real.pi / 6 ≤ (273402 / 1000000 : ℝ) := by linarith [Real.pi_gt_d6]
  have hp : (273402 / 1000000 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_d6]
  refine ⟨?_, ?_⟩
  · exact (Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hp hu).trans fixed_bounds.1
  · exact fixed_bounds.2.trans
      (Real.cos_le_cos_of_nonneg_of_le_pi h0 (by linarith [Real.pi_gt_d6]) hu)

private theorem product_sqrt_bound (t : ℝ) (ht : 2 ≤ t) (hT : t ≤ 63 / 25) :
    t * Real.sqrt (1 - (t / 4) ^ 2) ≤ 195703 / 100000 := by
  have htn : 0 ≤ t := by linarith
  have hq : t ^ 2 ≤ (63 / 25 : ℝ) ^ 2 := by nlinarith
  have hq0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hr : 0 ≤ 1 - (t / 4) ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg (1 - (t / 4) ^ 2)
  have hp0 : 0 ≤ t * Real.sqrt (1 - (t / 4) ^ 2) := mul_nonneg htn hs0
  have hd1 : 0 ≤ (63 / 25 : ℝ) ^ 2 - t ^ 2 := by linarith
  have hd2 : 0 ≤ 16 - (63 / 25 : ℝ) ^ 2 - t ^ 2 := by nlinarith
  have hp := mul_nonneg hd1 hd2
  have heq : (t * Real.sqrt (1 - (t / 4) ^ 2)) ^ 2 =
      t ^ 2 * (1 - t ^ 2 / 16) := by
    calc
      _ = t ^ 2 * (Real.sqrt (1 - (t / 4) ^ 2)) ^ 2 := by ring
      _ = t ^ 2 * (1 - t ^ 2 / 16) := by rw [hs]; ring
  nlinarith

private theorem cosine_comparison (t c : ℝ) (ht : 2 ≤ t) (hT : t ≤ 63 / 25)
    (hc : (96285 / 100000 : ℝ) ≤ Real.cos c)
    (hcs : Real.cos c ≤ 1)
    (hs : Real.sin c ≤ 27001 / 100000) :
    (t / 4) * Real.cos c - Real.sqrt (1 - (t / 4) ^ 2) * Real.sin c >
      t / 4 - (5876 / 10000 : ℝ) / t := by
  have htn : 0 < t := by linarith
  have hq : t ^ 2 ≤ (63 / 25 : ℝ) ^ 2 := by nlinarith
  have hp := product_sqrt_bound t ht hT
  have hp0 : 0 ≤ t * Real.sqrt (1 - (t / 4) ^ 2) :=
    mul_nonneg htn.le (Real.sqrt_nonneg _)
  have hprod1 : t ^ 2 / 4 * (1 - Real.cos c) ≤
      (63 / 25 : ℝ) ^ 2 / 4 * (1 - 96285 / 100000) := by
    have h1 : t ^ 2 / 4 * (1 - Real.cos c) ≤
        (63 / 25 : ℝ) ^ 2 / 4 * (1 - Real.cos c) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
    have h2 : (63 / 25 : ℝ) ^ 2 / 4 * (1 - Real.cos c) ≤
        (63 / 25 : ℝ) ^ 2 / 4 * (1 - 96285 / 100000) :=
      mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
    exact h1.trans h2
  have hprod2 : t * Real.sqrt (1 - (t / 4) ^ 2) * Real.sin c ≤
      (195703 / 100000 : ℝ) * (27001 / 100000) := by
    exact (mul_le_mul_of_nonneg_left hs hp0).trans
      (mul_le_mul_of_nonneg_right hp (by norm_num))
  have hmain : t ^ 2 / 4 * (1 - Real.cos c) +
      t * Real.sqrt (1 - (t / 4) ^ 2) * Real.sin c < 5876 / 10000 := by
    nlinarith
  have hm : t / 4 * (1 - Real.cos c) +
      Real.sqrt (1 - (t / 4) ^ 2) * Real.sin c < (5876 / 10000 : ℝ) / t := by
    apply (lt_div_iff₀ htn).2
    nlinarith [hmain]
  nlinarith [hm]

-- Source atn2 principal branch, for the acute triangle regime of source 8055810915.
private theorem kepler_atn2_arccos {d v w : ℝ} (hd : 0 < d) (hv : 0 < v)
    (hvd : v < d) (hw : 0 < w) (h : d ^ 2 + v ^ 2 = w ^ 2) :
    Real.pi / 2 + atn2 d (-v) = Real.arccos (v / w) := by
  have hbranch : |(-v)| < d := by simpa [abs_neg, abs_of_pos hv] using hvd
  rw [atn2, if_pos hbranch]
  have hr : Real.sqrt (1 - (v / w) ^ 2) = d / w := by
    apply (Real.sqrt_eq_iff_eq_sq ?_ (div_nonneg hd.le hw.le)).2
    · field_simp
      nlinarith [h]
    · have hless : v ^ 2 < w ^ 2 := by nlinarith [sq_pos_of_pos hd]
      rw [div_pow]
      exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hw)).mpr hless.le)
  rw [Real.arccos_eq_arctan (div_pos hv hw), hr]
  have hdiv : d / w / (v / w) = (v / d)⁻¹ := by field_simp
  rw [hdiv, Real.arctan_inv_of_pos (div_pos hv hd)]
  rw [neg_div, Real.arctan_neg]
  ring

-- Exact source 8055810915 has these positive triangle side lengths.
private theorem kepler_wazldcd_arclength_eq (t : ℝ) (ht : 2 ≤ t)
    (ht' : t ≤ (63 / 25 : ℝ)) :
    arclength t 2 (63 / 25) =
      Real.arccos ((t ^ 2 + 4 - (63 / 25 : ℝ) ^ 2) / (4 * t)) := by
  let v : ℝ := t ^ 2 + 4 - (63 / 25 : ℝ) ^ 2
  let u : ℝ := ups_x (t * t) (2 * 2) ((63 / 25) * (63 / 25))
  have htpos : 0 < t := by linarith
  have htlo : 4 ≤ t ^ 2 := by nlinarith
  have hthi : t ^ 2 ≤ (63 / 25 : ℝ) ^ 2 := by nlinarith
  have hv : 0 < v := by dsimp [v]; nlinarith
  have hvle : v ≤ 4 := by dsimp [v]; nlinarith
  have hu : u + v ^ 2 = (4 * t) ^ 2 := by dsimp [u, v, ups_x]; ring
  have hvltsq : v ^ 2 < u := by
    have hv2 : v ^ 2 ≤ 16 := by nlinarith
    nlinarith
  have hupos : 0 < u := by nlinarith [sq_nonneg v]
  have hd : 0 < Real.sqrt u := Real.sqrt_pos.mpr hupos
  have hbranch : v < Real.sqrt u := (Real.lt_sqrt hv.le).mpr hvltsq
  have heq : (Real.sqrt u) ^ 2 + v ^ 2 = (4 * t) ^ 2 := by
    rw [Real.sq_sqrt hupos.le]
    exact hu
  have hangle := kepler_atn2_arccos hd hv hbranch (by positivity : 0 < 4 * t) heq
  unfold arclength
  change Real.pi / 2 + atn2 (holSqrt u) ((63 / 25 : ℝ) * (63 / 25) - t * t - 2 * 2) = _
  have hsigned : holSqrt u = Real.sqrt u := by rw [holSqrt, if_pos hupos.le]
  rw [hsigned]
  have hminus : (63 / 25 : ℝ) * (63 / 25) - t * t - 2 * 2 = -v := by
    dsimp [v]
    ring
  rw [hminus]
  exact hangle

private theorem wazldcd_interval (t : ℝ) (ht : 2 ≤ t) (hT : t ≤ 63 / 25) :
    Real.arccos (t / 4) - Real.pi / 6 + 797 / 1000 < arclength t 2 (63 / 25) := by
  let c : ℝ := 797 / 1000 - Real.pi / 6
  have hc0 : 0 ≤ c := by dsimp [c]; linarith [Real.pi_lt_d6]
  have hcu : c ≤ 273402 / 1000000 := by dsimp [c]; linarith [Real.pi_gt_d6]
  have htn : 0 < t := by linarith
  have ht4 : t / 4 ≤ 1 := by linarith
  have ht0 : -1 ≤ t / 4 := by linarith
  have hbounds := delta_bounds
  have hcompare := cosine_comparison t c ht hT hbounds.2 (Real.cos_le_one c) hbounds.1
  have hcos : Real.cos (Real.arccos (t / 4) + c) >
      (t ^ 2 + 4 - (63 / 25 : ℝ) ^ 2) / (4 * t) := by
    rw [Real.cos_add, Real.cos_arccos ht0 ht4, Real.sin_arccos]
    have heq : (t ^ 2 + 4 - (63 / 25 : ℝ) ^ 2) / (4 * t) =
        t / 4 - (5876 / 10000 : ℝ) / t := by field_simp; ring
    rw [heq]
    exact hcompare
  have ha0 : 0 ≤ Real.arccos (t / 4) + c :=
    add_nonneg (Real.arccos_nonneg _) hc0
  have hau : Real.arccos (t / 4) + c ≤ Real.pi := by
    have hhalf : Real.arccos (t / 4) ≤ Real.pi / 2 :=
      Real.arccos_le_pi_div_two.mpr (by positivity)
    linarith [Real.pi_gt_d6]
  have hb0 : -1 ≤ (t ^ 2 + 4 - (63 / 25 : ℝ) ^ 2) / (4 * t) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * t)).2
    nlinarith
  have hangle := Real.arccos_lt_arccos hb0 hcos (Real.cos_le_one _)
  rw [Real.arccos_cos ha0 hau] at hangle
  rw [kepler_wazldcd_arclength_eq t ht hT]
  dsimp [c] at hangle
  linarith

end KeplerWazldcdProof

theorem solution : problem309.Valid := by
  change ∀ x : Fin 6 → ℝ, problem309.domain x → problem309.conclusion x
  intro x hx
  change inClosedIntervals _ at hx
  have hx0 : 4 ≤ x 0 ∧ x 0 ≤ (63 / 25 : ℝ) ^ 2 :=
    hx (4, x 0, (63 / 25) ^ 2) (by simp)
  have hx1' : 4 ≤ x 1 ∧ x 1 ≤ 4 := hx (4, x 1, 4) (by simp)
  have hx1 : x 1 = 4 := le_antisymm hx1'.2 hx1'.1
  have hx2 : x 2 = (63 / 25 : ℝ) ^ 2 := by
    have h : (2 * h0) ^ 2 ≤ x 2 ∧ x 2 ≤ (2 * h0) ^ 2 :=
      hx ((2 * h0) ^ 2, x 2, (2 * h0) ^ 2) (by simp)
    norm_num [h0] at h ⊢
    exact le_antisymm h.2 h.1
  have hnonneg : 0 ≤ x 0 := by linarith [hx0.1]
  have hsqrt : Real.sqrt (x 0) ^ 2 = x 0 := Real.sq_sqrt hnonneg
  have hlow : 2 ≤ Real.sqrt (x 0) := by
    nlinarith [Real.sqrt_nonneg (x 0)]
  have hupp : Real.sqrt (x 0) ≤ 63 / 25 := by
    nlinarith [Real.sqrt_nonneg (x 0)]
  have hroot0 : holSqrt (x 0) = Real.sqrt (x 0) := by simp [holSqrt, hnonneg]
  have hroot1 : holSqrt (x 1) = 2 := by
    rw [hx1]
    rw [holSqrt, if_pos (by norm_num : (0 : ℝ) ≤ 4)]
    convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1
    norm_num
  have hroot2 : holSqrt (x 2) = 63 / 25 := by
    rw [hx2]
    rw [holSqrt, if_pos (sq_nonneg _),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 63 / 25)]
  change Real.arccos (holSqrt (x 0) / 4) - Real.pi / 6 + 797 / 1000 <
    arclength (holSqrt (x 0)) (holSqrt (x 1)) (holSqrt (x 2))
  rw [hroot0, hroot1, hroot2]
  exact KeplerWazldcdProof.wazldcd_interval _ hlow hupp
