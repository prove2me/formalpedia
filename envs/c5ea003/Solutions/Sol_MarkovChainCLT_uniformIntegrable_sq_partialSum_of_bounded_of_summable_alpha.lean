-- Prove2me | solution 1 for MarkovChainCLT.uniformIntegrable_sq_partialSum_of_bounded_of_summable_alpha
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:21:02.513048+00:00
-- url     : https://prove2.me/submissions/1a7345c7-0dda-48ba-a685-a6ab9962476b

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring
import Theorems.Thm_MarkovChainCLT_clt_of_bounded_of_summable_alpha
import Theorems.Thm_MarkovChainCLT_tendsto_inv_mul_integral_sq_partialSum
import Theorems.Thm_MarkovChainCLT_clt_iff_uniformlyIntegrable_of_alpha_mixing

/- Bounded strongly mixing partial sums: uniform integrability.
All three new local component bodies are included in full. The accepted
bounded CLT, second-moment asymptotic and forward Denker implication are
used through their registered public theorem interfaces. No earlier private
proof helper is imported, and no uniform-integrability premise is assumed. -/

section BoundedUIComponent1

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace BoundedUiNormalization

theorem gaussian_limit_varying_mul {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (U : Nat → Omega → Real)
    (v : NNReal)
    (hU : TendstoInDistribution U atTop (id : Real → Real) (fun _ => P) (gaussianReal 0 v))
    (a : Nat → Real) (c : Real) (ha : Tendsto a atTop (nhds c))
    (hscale : c ^ 2 * (v : Real) = 1) :
    TendstoInDistribution (fun n w => a n * U n w) atTop (id : Real → Real)
      (fun _ => P) (gaussianReal 0 1) := by
  have haMeasure : TendstoInMeasure P (fun n _ => a n) atTop (fun _ => c) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Filter.Eventually.of_forall (fun _ => ha))
  have hscaled := hU.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : Real × Real => z.2 * z.1) (by fun_prop) haMeasure
    (fun _ => aemeasurable_const)
  have hnn : NNReal.mk (c ^ 2) (sq_nonneg c) * v = 1 := by
    apply Subtype.ext
    exact hscale
  have hmap : (gaussianReal 0 v).map (fun x => c * x) = gaussianReal 0 1 := by
    simpa only [mul_zero, hnn] using (gaussianReal_map_const_mul (μ := 0) (v := v) c)
  refine ⟨hscaled.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
  simpa only [Function.comp_def, id_eq, hmap, Measure.map_id] using hscaled.tendsto

end BoundedUiNormalization

end BoundedUIComponent1

section BoundedUIComponent2

open Filter
open scoped Topology

namespace BoundedUINormalization

noncomputable def normalizationFactor (V : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt ((n : ℝ)⁻¹ * V n))⁻¹

lemma variance_tendsto_atTop (V : ℕ → ℝ) (v : ℝ) (hv : 0 < v)
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * V n) atTop (𝓝 v)) :
    Tendsto V atTop atTop := by
  have hprod : Tendsto (fun n : ℕ => (n : ℝ) * ((n : ℝ)⁻¹ * V n)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_mul_pos hv h
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  simp [hn0]

lemma normalizationFactor_tendsto (V : ℕ → ℝ) (v : ℝ) (hv : 0 < v)
    (h : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * V n) atTop (𝓝 v)) :
    Tendsto (normalizationFactor V) atTop (𝓝 (Real.sqrt v)⁻¹) := by
  exact h.sqrt.inv₀ (Real.sqrt_pos.2 hv).ne'

lemma normalization_eq (V : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (S : ℝ) :
    normalizationFactor V n * ((Real.sqrt n)⁻¹ * S) = S / Real.sqrt (V n) := by
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.2 (Nat.cast_pos.2 hn)).ne'
  rw [normalizationFactor, Real.sqrt_mul (inv_nonneg.2 (Nat.cast_nonneg n)),
    Real.sqrt_inv, mul_inv_rev, inv_inv]
  calc
    (Real.sqrt (V n))⁻¹ * Real.sqrt (n : ℝ) * ((Real.sqrt n)⁻¹ * S) =
        (Real.sqrt (V n))⁻¹ * (Real.sqrt (n : ℝ) * (Real.sqrt n)⁻¹) * S := by ring
    _ = S / Real.sqrt (V n) := by
      rw [mul_inv_cancel₀ hn0]
      simp [div_eq_mul_inv, mul_comm]

lemma eventually_normalization_eq (V : ℕ → ℝ) :
    ∀ᶠ n in atTop, ∀ S : ℝ,
      normalizationFactor V n * ((Real.sqrt n)⁻¹ * S) = S / Real.sqrt (V n) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn S
  exact normalization_eq V n hn S

lemma inv_sqrt_sq_mul (v : ℝ) (hv : 0 < v) :
    ((Real.sqrt v)⁻¹) ^ 2 * v = 1 := by
  rw [inv_pow, Real.sq_sqrt hv.le]
  exact inv_mul_cancel₀ hv.ne'

end BoundedUINormalization

end BoundedUIComponent2

section BoundedUIComponent3

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0)
    (B : ℝ) (hB : ∀ n, ∀ᵐ ω ∂P, |Y n ω| < B)
    (hα : Summable (fun n => alphaMixingCoef P Y n))
    (hvar : 0 < seqAsymptoticVariance P Y) :
    UniformIntegrable
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) ^ 2
        / ∫ ω', (∑ i ∈ Finset.range n, Y i ω') ^ 2 ∂P) 1 P := by
  have hL2 : MemLp (Y 0) 2 P :=
    MemLp.of_bound (hY 0).aestronglyMeasurable B
      ((hB 0).mono (fun _ hw => by simpa only [Real.norm_eq_abs] using hw.le))
  obtain ⟨hsum, hclt⟩ := clt_of_bounded_of_summable_alpha P Y hY hstat hcent B hB hα
  let V : ℕ → ℝ := fun n => ∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 2 ∂P
  have hratio : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * V n) atTop
      (𝓝 (seqAsymptoticVariance P Y)) :=
    tendsto_inv_mul_integral_sq_partialSum P Y hY hstat hL2 hsum
  have hdiverge := BoundedUINormalization.variance_tendsto_atTop V
    (seqAsymptoticVariance P Y) hvar hratio
  have hfactor := BoundedUINormalization.normalizationFactor_tendsto V
    (seqAsymptoticVariance P Y) hvar hratio
  have hscale : ((Real.sqrt (seqAsymptoticVariance P Y))⁻¹) ^ 2 *
      ((seqAsymptoticVariance P Y).toNNReal : ℝ) = 1 := by
    rw [Real.coe_toNNReal _ hvar.le]
    exact BoundedUINormalization.inv_sqrt_sq_mul _ hvar
  have hscaled := BoundedUiNormalization.gaussian_limit_varying_mul P
    (fun n ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
    (seqAsymptoticVariance P Y).toNNReal (hclt hvar)
    (BoundedUINormalization.normalizationFactor V)
    (Real.sqrt (seqAsymptoticVariance P Y))⁻¹ hfactor hscale
  have hnormalized : TendstoInDistribution
      (fun (n : ℕ) ω => (∑ i ∈ Finset.range n, Y i ω) / Real.sqrt (V n))
      atTop (id : ℝ → ℝ) (fun _ => P) (gaussianReal 0 1) := by
    refine hscaled.congr (fun n => ae_of_all _ (fun ω => ?_)) (ae_of_all _ (fun _ => rfl))
    by_cases hn : n = 0
    · simp [hn]
    · exact BoundedUINormalization.normalization_eq V n (Nat.pos_of_ne_zero hn) _
  exact (clt_iff_uniformlyIntegrable_of_alpha_mixing P Y hY hstat hcent hL2
    hα.tendsto_atTop_zero hdiverge).mp hnormalized

end BoundedUIComponent3

