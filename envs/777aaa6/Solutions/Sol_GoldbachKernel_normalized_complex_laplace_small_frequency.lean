-- Prove2me | solution 1 for GoldbachKernel_normalized_complex_laplace_small_frequency
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T06:17:09.096087+00:00
-- url     : https://prove2.me/submissions/0076b4a0-0523-4b22-9179-b8bc7378ca54

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

open MeasureTheory Set
set_option autoImplicit false

private lemma covariance_inner (w f g : ℝ → ℝ) (hw : Continuous w)
    (hf : Continuous f) (hg : Continuous g) (v : ℝ) :
    (∫ u in (0:ℝ)..2, w u*(f u-f v)*(g u-g v)) =
      (∫ u in (0:ℝ)..2, w u*f u*g u) -
      f v*(∫ u in (0:ℝ)..2, w u*g u) -
      g v*(∫ u in (0:ℝ)..2, w u*f u) +
      (f v*g v)*(∫ u in (0:ℝ)..2, w u) := by
  have ha := ((hw.mul hf).mul hg).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hb := ((hw.mul hg).const_mul (f v)).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hc := ((hw.mul hf).const_mul (g v)).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hd := (hw.const_mul (f v*g v)).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  simp only [Pi.mul_apply] at ha hb hc hd
  change IntervalIntegrable (fun u => w u*f u*g u) volume (0:ℝ) 2 at ha
  calc
    _ = ∫ u in (0:ℝ)..2, w u*f u*g u-f v*(w u*g u)-g v*(w u*f u)+(f v*g v)*w u := by
      apply intervalIntegral.integral_congr
      intro u _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add ((ha.sub hb).sub hc) hd,
        intervalIntegral.integral_sub (ha.sub hb) hc,
        intervalIntegral.integral_sub ha hb]
      simp only [intervalIntegral.integral_const_mul]

-- Weighted integral Chebyshev inequality for two antitone functions.
private lemma antitone_weighted_integral_covariance (w f g : ℝ → ℝ)
    (hw : Continuous w) (hf : Continuous f) (hg : Continuous g)
    (hwpos : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ w u)
    (hfa : AntitoneOn f (Icc (0:ℝ) 2)) (hga : AntitoneOn g (Icc (0:ℝ) 2)) :
    0 ≤ (∫ u in (0:ℝ)..2, w u*f u*g u)*(∫ u in (0:ℝ)..2, w u) -
      (∫ u in (0:ℝ)..2, w u*f u)*(∫ u in (0:ℝ)..2, w u*g u) := by
  have hdiff (u v : ℝ) (hu : u ∈ Icc (0:ℝ) 2) (hv : v ∈ Icc (0:ℝ) 2) :
      0 ≤ (f u-f v)*(g u-g v) := by
    by_cases h : u ≤ v
    · exact mul_nonneg (sub_nonneg.mpr (hfa hu hv h)) (sub_nonneg.mpr (hga hu hv h))
    · exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr (hfa hv hu (le_of_not_ge h)))
        (sub_nonpos.mpr (hga hv hu (le_of_not_ge h)))
  have hdouble : 0 ≤ ∫ v in (0:ℝ)..2, w v*(∫ u in (0:ℝ)..2, w u*(f u-f v)*(g u-g v)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro v hv
    apply mul_nonneg (hwpos v hv)
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    simpa only [mul_assoc] using mul_nonneg (hwpos u hu) (hdiff u v hu hv)
  simp_rw [covariance_inner w f g hw hf hg] at hdouble
  let A := ∫ u in (0:ℝ)..2, w u*f u*g u
  let B := ∫ u in (0:ℝ)..2, w u*g u
  let C := ∫ u in (0:ℝ)..2, w u*f u
  let D := ∫ u in (0:ℝ)..2, w u
  have ha := (hw.const_mul A).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hb := ((hw.mul hf).const_mul B).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hc := ((hw.mul hg).const_mul C).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  have hd := (((hw.mul hf).mul hg).const_mul D).intervalIntegrable (μ := volume) (a := (0:ℝ)) (b := 2)
  simp only [Pi.mul_apply] at ha hb hc hd
  have heq : (∫ v in (0:ℝ)..2, w v*(A-f v*B-g v*C+(f v*g v)*D)) = 2*(A*D-C*B) := by
    calc
      _ = ∫ v in (0:ℝ)..2, A*w v-B*(w v*f v)-C*(w v*g v)+D*(w v*f v*g v) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add ((ha.sub hb).sub hc) hd,
          intervalIntegral.integral_sub (ha.sub hb) hc,
          intervalIntegral.integral_sub ha hb]
        simp only [intervalIntegral.integral_const_mul]
        change A*D-B*C-C*B+D*A = _
        ring
  change 0 ≤ ∫ v in (0:ℝ)..2, w v*(A-f v*B-g v*C+(f v*g v)*D) at hdouble
  rw [heq] at hdouble
  change 0 ≤ A*D-C*B
  linarith

-- Small-frequency normalized cosine comparison for any continuous nonnegative kernel.
private lemma normalized_cosine_tilt_mono (kernel : ℝ → ℝ) (hk : Continuous kernel)
    (hkpos : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ kernel u)
    (r s frequency : ℝ) (hrs : r ≤ s) (ht : 0 ≤ frequency) (htop : frequency ≤ Real.pi/2)
    (hrden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u))
    (hsden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) :
    (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)*Real.cos (frequency*u)) /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)) ≤
    (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)*Real.cos (frequency*u)) /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) := by
  let w : ℝ → ℝ := fun u => kernel u*Real.exp (-r*u)
  let f : ℝ → ℝ := fun u => Real.exp (-(s-r)*u)
  let g : ℝ → ℝ := fun u => Real.cos (frequency*u)
  have hw : Continuous w := by fun_prop
  have hf : Continuous f := by fun_prop
  have hg : Continuous g := by fun_prop
  have hwp : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ w u :=
    fun u hu => mul_nonneg (hkpos u hu) (Real.exp_pos _).le
  have hfa : AntitoneOn f (Icc (0:ℝ) 2) := by
    intro u hu v hv huv
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left huv (by linarith)
  have hga : AntitoneOn g (Icc (0:ℝ) 2) := by
    intro u hu v hv huv
    apply Real.antitoneOn_cos
    · exact ⟨mul_nonneg ht hu.1,by nlinarith [hu.2]⟩
    · exact ⟨mul_nonneg ht hv.1,by nlinarith [hv.2]⟩
    · exact mul_le_mul_of_nonneg_left huv ht
  have hwf (u : ℝ) : w u*f u = kernel u*Real.exp (-s*u) := by
    dsimp only [w,f]
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  have hwfg (u : ℝ) : w u*f u*g u = kernel u*Real.exp (-s*u)*Real.cos (frequency*u) := by
    rw [hwf]
  have hc := antitone_weighted_integral_covariance w f g hw hf hg hwp hfa hga
  simp_rw [hwfg,hwf] at hc
  dsimp only [w,g] at hc
  apply (div_le_div_iff₀ hrden hsden).mpr
  nlinarith

private lemma normalized_cosine_tilt_mono_abs (kernel : ℝ → ℝ) (hk : Continuous kernel)
    (hkpos : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ kernel u)
    (r s frequency : ℝ) (hrs : r ≤ s) (ht : |frequency| ≤ Real.pi/2)
    (hrden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u))
    (hsden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) :
    (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)*Real.cos (frequency*u)) /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)) ≤
    (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)*Real.cos (frequency*u)) /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) := by
  by_cases hfreq : 0 ≤ frequency
  · exact normalized_cosine_tilt_mono kernel hk hkpos r s frequency hrs hfreq
      (by simpa [abs_of_nonneg hfreq] using ht) hrden hsden
  · have hneg : frequency ≤ 0 := le_of_not_ge hfreq
    have h := normalized_cosine_tilt_mono kernel hk hkpos r s (-frequency) hrs
      (neg_nonneg.mpr hneg) (by simpa [abs_of_nonpos hneg] using ht) hrden hsden
    simpa only [neg_mul,Real.cos_neg] using h

private lemma complex_laplace_real_part (kernel : ℝ → ℝ) (hk : Continuous kernel)
    (r frequency : ℝ) :
    ((∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
      (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re =
      ∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)*Real.cos (frequency*u) := by
  have hf : IntervalIntegrable (fun u : ℝ => (kernel u:ℂ)*Complex.exp
      (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) volume (0:ℝ) 2 :=
    (by fun_prop : Continuous (fun u : ℝ => (kernel u:ℂ)*Complex.exp
      (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ)))).intervalIntegrable (μ := volume) 0 2
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hf
  change Complex.reCLM (∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
    (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) = _
  calc
    _ = ∫ u in (0:ℝ)..2, Complex.reCLM ((kernel u:ℂ)*Complex.exp
        (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) := by exact hmap.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      change ((kernel u:ℂ)*Complex.exp
        (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))).re = _
      simp [Complex.mul_re,Complex.mul_im,Complex.exp_re,Real.cos_neg]
      ring

theorem solution (kernel : ℝ → ℝ) (hk : Continuous kernel)
    (hkpos : ∀ u ∈ Icc (0:ℝ) 2, 0 ≤ kernel u)
    (r s frequency : ℝ) (hrs : r ≤ s) (ht : |frequency| ≤ Real.pi/2)
    (hrden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u))
    (hsden : 0 < ∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) :
    ((∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
      (-((r:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-r*u)) ≤
    ((∫ u in (0:ℝ)..2, (kernel u:ℂ)*Complex.exp
      (-((s:ℂ)+(frequency:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, kernel u*Real.exp (-s*u)) := by
  rw [complex_laplace_real_part kernel hk r frequency,
    complex_laplace_real_part kernel hk s frequency]
  exact normalized_cosine_tilt_mono_abs kernel hk hkpos r s frequency hrs ht hrden hsden

#print axioms solution
