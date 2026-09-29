-- Prove2me | solution 1 for MarkovChainCLT.tendstoInDistribution_inv_sqrt_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T07:50:25.500921+00:00
-- url     : https://prove2.me/submissions/fa820d4d-56e3-400b-9ad4-11f339514d4c

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

/-!
# Changing the normalisation from `d n` to `√n`
-/

variable {Ω : Type*} [MeasurableSpace Ω]

namespace SqrtNormAux

/-- A sequence of constants converging to `s` converges to `s` in measure. -/
theorem tendstoInMeasure_const_of_tendsto (P : Measure Ω) (c : ℕ → ℝ) (s : ℝ)
    (hc : Tendsto c atTop (𝓝 s)) :
    TendstoInMeasure P (fun n (_ : Ω) => c n) atTop (fun _ => s) := by
  refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
  have hzero : ∀ᶠ n in atTop, P {ω : Ω | ε ≤ dist (c n) s} = 0 := by
    filter_upwards [hc (Metric.ball_mem_nhds s hε)] with n hn
    have hset : {ω : Ω | ε ≤ dist (c n) s} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      simpa [Metric.mem_ball, dist_comm] using hn
    rw [hset, measure_empty]
  exact Tendsto.congr' (by filter_upwards [hzero] with n hn; rw [hn]) tendsto_const_nhds

/-- Two sequences that agree eventually differ by something converging to `0` in measure. -/
theorem tendstoInMeasure_sub_of_eventuallyEq (P : Measure Ω) (U V : ℕ → Ω → ℝ)
    (h : ∀ᶠ n in atTop, ∀ ω, V n ω = U n ω) :
    TendstoInMeasure P (V - U) atTop 0 := by
  refine tendstoInMeasure_iff_dist.2 fun ε hε => ?_
  have hzero : ∀ᶠ n in atTop,
      P {ω : Ω | ε ≤ dist ((V - U) n ω) ((0 : Ω → ℝ) ω)} = 0 := by
    filter_upwards [h] with n hn
    have hset : {ω : Ω | ε ≤ dist ((V - U) n ω) ((0 : Ω → ℝ) ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le, Pi.sub_apply,
        Pi.zero_apply]
      rw [hn ω]
      simpa using hε
    rw [hset, measure_empty]
  exact Tendsto.congr' (by filter_upwards [hzero] with n hn; rw [hn]) tendsto_const_nhds

end SqrtNormAux

open SqrtNormAux in
/-- If `X n / d n` converges in distribution to a standard Gaussian and `d n / √n → s > 0`,
then `X n / √n` converges in distribution to `N(0, s²)`. -/
theorem solution (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (d : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hX : ∀ n, Measurable (X n))
    (hd : Tendsto (fun n : ℕ => d n / Real.sqrt n) atTop (𝓝 s))
    (hnorm : TendstoInDistribution (fun (n : ℕ) ω => X n ω / d n) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * X n ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 (Real.toNNReal (s ^ 2))) := by
  set c : ℕ → ℝ := fun n => d n / Real.sqrt n with hc
  -- Slutsky: multiplying by the convergent scalars `c n`
  have hcm : TendstoInMeasure P (fun n (_ : Ω) => c n) atTop (fun _ => s) :=
    tendstoInMeasure_const_of_tendsto P c s hd
  have hU : TendstoInDistribution (fun (n : ℕ) ω => c n * (X n ω / d n)) atTop
      (fun ω : ℝ => s * ω) (fun _ => P) (gaussianReal 0 1) :=
    hnorm.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun x : ℝ × ℝ => x.2 * x.1) (by fun_prop) hcm (fun _ => aemeasurable_const)
  -- eventually `d n ≠ 0`, and then the two normalisations agree
  have hdne : ∀ᶠ n : ℕ in atTop, d n ≠ 0 := by
    have h2 : ∀ᶠ n : ℕ in atTop, s / 2 < c n :=
      hd.eventually_const_lt (by linarith : s / 2 < s)
    filter_upwards [h2] with n hn hzero
    have : c n = 0 := by simp [hc, hzero]
    rw [this] at hn
    linarith
  have heq : ∀ᶠ n : ℕ in atTop, ∀ ω, (Real.sqrt n)⁻¹ * X n ω = c n * (X n ω / d n) := by
    filter_upwards [hdne] with n hn ω
    simp only [hc]
    field_simp
  have hV : TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * X n ω) atTop
      (fun ω : ℝ => s * ω) (fun _ => P) (gaussianReal 0 1) :=
    tendstoInDistribution_of_tendstoInMeasure_sub _ _ hU
      (tendstoInMeasure_sub_of_eventuallyEq P _ _ heq)
      (fun n => ((measurable_const.mul (hX n)).aemeasurable))
  -- identify the limit law: the image of `N(0,1)` under `x ↦ s x` is `N(0, s²)`
  have hmap : (gaussianReal 0 1).map (fun ω : ℝ => s * ω)
      = (gaussianReal 0 (Real.toNNReal (s ^ 2))).map (id : ℝ → ℝ) := by
    have h1 : (gaussianReal 0 1).map (fun ω : ℝ => s * ω)
        = gaussianReal (s * 0) (⟨s ^ 2, sq_nonneg s⟩ * 1) :=
      gaussianReal_map_const_mul (μ := 0) (v := 1) s
    have h2 : (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) = Real.toNNReal (s ^ 2) := by
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg s)]
    rw [h1, h2, Measure.map_id, mul_one, mul_zero]
  refine ⟨hV.forall_aemeasurable, by fun_prop, ?_⟩
  have h := hV.tendsto
  convert h using 2
  exact Subtype.ext (by simpa using hmap.symm)
