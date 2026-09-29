-- Prove2me | solution 2 for MarkovChainCLT.tendstoInDistribution_inv_sqrt_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T08:17:22.801994+00:00
-- url     : https://prove2.me/submissions/a2e93412-8af2-4919-80a3-ba239af15467

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (d : ℕ → ℝ) (s : ℝ) (hs : 0 < s)
    (hX : ∀ n, Measurable (X n))
    (hd : Tendsto (fun n : ℕ => d n / Real.sqrt n) atTop (𝓝 s))
    (hnorm : TendstoInDistribution (fun (n : ℕ) ω => X n ω / d n) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 1)) :
    TendstoInDistribution (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * X n ω) atTop (id : ℝ → ℝ) (fun _ => P)
      (gaussianReal 0 (Real.toNNReal (s ^ 2))) := by
  have hXmeas : ∀ n : ℕ, Measurable (fun ω => (Real.sqrt n)⁻¹ * X n ω) :=
    fun n => by fun_prop
  have hYmeas : ∀ n, Measurable (fun _ : Ω => d n / Real.sqrt n) :=
    fun n => by fun_prop
  have hYlim : TendstoInMeasure P (fun n _ => d n / Real.sqrt n) atTop (fun _ => s) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n => aestronglyMeasurable_const)
    exact Filter.Eventually.of_forall fun _ => hd
  have hSlutsky : TendstoInDistribution (fun n ω => X n ω / d n * (d n / Real.sqrt n)) atTop
      (fun ω => id ω * s) (fun _ => P) (gaussianReal 0 1) :=
    hnorm.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.1 * p.2) continuous_mul hYlim
      (fun n => (hYmeas n).aemeasurable)
  have hmap : (gaussianReal 0 1).map (fun ω : ℝ => id ω * s)
      = gaussianReal 0 (Real.toNNReal (s ^ 2)) := by
    have e : (fun ω : ℝ => id ω * s) = (s * ·) := by
      funext ω; simp [mul_comm]
    rw [e, gaussianReal_map_const_mul, mul_zero]
    congr 1
    rw [mul_one]
    apply Subtype.ext
    exact (Real.coe_toNNReal _ (sq_nonneg s)).symm
  have hev : ∀ᶠ n in atTop, d n ≠ 0 ∧ 1 ≤ n := by
    have hpos : ∀ᶠ n in atTop, d n / Real.sqrt n ∈ Set.Ioi 0 :=
      hd.eventually (Ioi_mem_nhds hs)
    filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
    refine ⟨?_, hn1⟩
    intro h0
    rw [h0, zero_div] at hn
    simp at hn
  have hlim_meas : AEMeasurable (id : ℝ → ℝ) (gaussianReal 0 (Real.toNNReal (s ^ 2))) :=
    measurable_id.aemeasurable
  have hPtval : (gaussianReal 0 1).map (fun ω : ℝ => id ω * s)
      = (gaussianReal 0 (Real.toNNReal (s ^ 2))).map id := by
    rw [hmap, Measure.map_id]
  have hPt : (⟨(gaussianReal 0 1).map (fun ω : ℝ => id ω * s),
      Measure.isProbabilityMeasure_map hSlutsky.aemeasurable_limit⟩ : ProbabilityMeasure ℝ)
      = ⟨(gaussianReal 0 (Real.toNNReal (s ^ 2))).map id,
      Measure.isProbabilityMeasure_map hlim_meas⟩ :=
    Subtype.ext hPtval
  have hStep1 := hPt ▸ hSlutsky.tendsto
  have hmaps : ∀ᶠ n in atTop, (⟨P.map (fun ω => X n ω / d n * (d n / Real.sqrt n)),
        Measure.isProbabilityMeasure_map (hSlutsky.forall_aemeasurable n)⟩ : ProbabilityMeasure ℝ)
      = ⟨P.map (fun ω => (Real.sqrt n)⁻¹ * X n ω),
        Measure.isProbabilityMeasure_map (hXmeas n).aemeasurable⟩ := by
    filter_upwards [hev] with n ⟨hdn, hn1⟩
    have hfun : (fun ω => X n ω / d n * (d n / Real.sqrt n))
        = (fun ω => (Real.sqrt n)⁻¹ * X n ω) := by
      funext ω
      rw [div_mul_div_comm, mul_comm (d n) (Real.sqrt n),
        mul_div_mul_right _ _ hdn, div_eq_inv_mul]
    exact Subtype.ext (show P.map (fun ω => X n ω / d n * (d n / Real.sqrt n))
      = P.map (fun ω => (Real.sqrt n)⁻¹ * X n ω) from by rw [hfun])
  have hfin := hStep1.congr' hmaps
  exact ⟨fun n => (hXmeas n).aemeasurable, measurable_id.aemeasurable, hfin⟩
