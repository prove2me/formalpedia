-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_hypercube_minimax_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:31:42.408461+00:00
-- url     : https://prove2.me/submissions/f8b36274-0095-4049-b324-ea92a055da4b

import Definitions.Def_LinearBanditProtocol
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic
import Theorems.Thm_BanditAlgorithm_bretagnolle_huber_inequality
import Mathlib.MeasureTheory.Integral.Bochner.Set

/- Complete attributed Gaussian KL helpers and all new cube-support,
geometry, and regret arguments are inlined. Exact provenance: assembly.json. -/

/- Complete accepted Gaussian formula by Harry_Xu, submission
10bebc7c-083f-4815-8d48-f7041d8f3b3b; canonical declaration rename only.
Generic Gaussian kernel/KL block by Harry_Xu, submission
c04edc73-6da4-4fd6-91f2-a0ed33ec6f61, copied verbatim from lines 419-885.
See gaussian-selection.json for original source and exact segment hashes. -/

open MeasureTheory ProbabilityTheory InformationTheory NNReal

/-!
Source: Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020), Section 14.2,
printed p. 189 (PDF p. 198), immediately after Eq. (14.6). For Gaussian
probability measures with means `mu1`, `mu2` and common positive variance `v`,
the log-density ratio is affine in the sample. Integrating it under the first
Gaussian leaves `(mu1 - mu2)^2 / (2 * v)`.
-/

theorem BanditAlgorithm.gaussian_relative_entropy_formula (mu1 mu2 : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal mu1 v) (gaussianReal mu2 v) =
      ENNReal.ofReal ((mu1 - mu2) ^ 2 / (2 * (v : ℝ))) := by
  let P := gaussianReal mu1 v
  let Q := gaussianReal mu2 v
  have hPvol : P ≪ volume := gaussianReal_absolutelyContinuous mu1 hv
  have hvolQ : volume ≪ Q := gaussianReal_absolutelyContinuous' mu2 hv
  have hPQ : P ≪ Q := hPvol.trans hvolQ
  have hQvol : Q ≪ volume := gaussianReal_absolutelyContinuous mu2 hv
  have hratio :
      P.rnDeriv Q =ᵐ[Q] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x := by
    filter_upwards [Measure.rnDeriv_eq_div hPvol hQvol,
      hQvol (rnDeriv_gaussianReal mu1 v), hQvol (rnDeriv_gaussianReal mu2 v)]
      with x hx h1 h2
    rw [hx, h1, h2]
  have hratioP :
      P.rnDeriv Q =ᵐ[P] fun x => gaussianPDF mu1 v x / gaussianPDF mu2 v x :=
    hPQ hratio
  have hllr : llr P Q =ᵐ[P] fun x =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) := by
    filter_upwards [hratioP] with x hx
    rw [llr, hx]
    simp only [ENNReal.toReal_div, toReal_gaussianPDF]
    rw [gaussianPDFReal, gaussianPDFReal]
    have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have hc : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≠ 0 := by
      positivity
    rw [mul_div_mul_left _ _ hc, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
      Real.log_exp, Real.log_exp]
    field_simp
    ring
  have hid : Integrable (fun x : ℝ => x) P := by
    simpa [P] using (memLp_id_gaussianReal (μ := mu1) (v := v) 1).integrable (by simp)
  have haff : Integrable (fun x : ℝ =>
      ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ))) P := by
    have hlin : Integrable (fun x : ℝ =>
        (2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2)) / (2 * (v : ℝ))) P :=
      ((hid.const_mul (2 * (mu1 - mu2))).add (integrable_const _)).div_const _
    exact hlin.congr (ae_of_all _ fun x => by ring)
  have hllr_int : Integrable (llr P Q) P := haff.congr hllr.symm
  rw [klDiv_of_ac_of_integrable hPQ hllr_int]
  congr 1
  simp only [P, Q, probReal_univ, add_sub_cancel_right]
  rw [integral_congr_ae hllr]
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  calc
    (∫ x, ((x - mu2) ^ 2 - (x - mu1) ^ 2) / (2 * (v : ℝ)) ∂P) =
        (2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2)) /
          (2 * (v : ℝ)) := by
            rw [integral_div]
            congr 1
            calc
              (∫ x, (x - mu2) ^ 2 - (x - mu1) ^ 2 ∂P) =
                  ∫ x, 2 * (mu1 - mu2) * x + (mu2 ^ 2 - mu1 ^ 2) ∂P := by
                    apply integral_congr_ae
                    exact ae_of_all _ fun x => by ring
              _ = 2 * (mu1 - mu2) * (∫ x, x ∂P) + (mu2 ^ 2 - mu1 ^ 2) := by
                    rw [integral_add (hid.const_mul _) (integrable_const _),
                      integral_const_mul, integral_const]
                    simp
    _ = (mu1 - mu2) ^ 2 / (2 * (v : ℝ)) := by
          simp [P, integral_id_gaussianReal]
          ring

open MeasureTheory ProbabilityTheory InformationTheory
open Matrix

namespace BanditAlgorithm

attribute [local instance] Classical.propDecidable

private noncomputable def shiftedGaussianKernel
    {α : Type*} [MeasurableSpace α] (m : α → ℝ) (hm : Measurable m) :
    Kernel α ℝ :=
  ((Kernel.id : Kernel α α).compProd
      (Kernel.const (α × α) (gaussianReal 0 1))).map
    (fun p ↦ m p.1 + p.2)

private instance shiftedGaussianKernel.instIsMarkovKernel
    {α : Type*} [MeasurableSpace α] (m : α → ℝ) (hm : Measurable m) :
    IsMarkovKernel (shiftedGaussianKernel m hm) := by
  unfold shiftedGaussianKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

private theorem shiftedGaussianKernel_apply
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : α → ℝ) (hm : Measurable m)
    (a : α) :
    shiftedGaussianKernel m hm a = gaussianReal (m a) 1 := by
  rw [shiftedGaussianKernel, Kernel.map_apply]
  · rw [Kernel.compProd_apply_eq_compProd_sectR]
    simp only [Kernel.id_apply]
    have hprod :
        Measure.dirac a ⊗ₘ
            (Kernel.const (α × α) (gaussianReal 0 1)).sectR a =
          (gaussianReal 0 1).map (Prod.mk a) := by
      ext s hs
      rw [Measure.dirac_compProd_apply hs]
      rw [Kernel.sectR_apply, Kernel.const_apply,
        Measure.map_apply measurable_prodMk_left hs]
    rw [hprod]
    have hg : Measurable (fun p : α × ℝ ↦ m p.1 + p.2) :=
      (hm.comp measurable_fst).add measurable_snd
    rw [Measure.map_map hg measurable_prodMk_left]
    simpa [Function.comp_def] using
      (gaussianReal_map_const_add (μ := 0) (v := 1) (m a))
  · fun_prop

private theorem compProd_shiftedGaussianKernel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [SFinite μ]
    (m : α → ℝ) (hm : Measurable m) :
    μ.compProd (shiftedGaussianKernel m hm) =
      (μ.compProd (Kernel.const α (gaussianReal 0 1))).map
        (fun p ↦ (p.1, m p.1 + p.2)) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.map_apply (by fun_prop) hs]
  rw [Measure.compProd_apply (hs.preimage (by fun_prop))]
  apply lintegral_congr
  intro a
  rw [shiftedGaussianKernel_apply m hm a]
  simp only [Kernel.const_apply]
  rw [show gaussianReal (m a) 1 =
      (gaussianReal 0 1).map (fun z ↦ m a + z) by
        simpa using (gaussianReal_map_const_add (μ := 0) (v := 1) (m a)).symm]
  rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

private noncomputable def linearStepKernel {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    Kernel (LinearBanditHistory d k) ((Fin d → ℝ) × ℝ) :=
  ((π.select k).compProd
      (Kernel.const (LinearBanditHistory d k × (Fin d → ℝ))
        (gaussianReal 0 1))).map
    (fun p ↦ (p.1, p.1 ⬝ᵥ θ + p.2))

private instance linearStepKernel.instIsMarkovKernel {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    IsMarkovKernel (linearStepKernel (k := k) θ π) := by
  unfold linearStepKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

private theorem linearStepKernel_apply {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (h : LinearBanditHistory d k) :
    linearStepKernel (k := k) θ π h =
      (π.select k h).compProd
        (shiftedGaussianKernel
          (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
          (Finset.measurable_sum _ fun i _ ↦
            (measurable_pi_apply i).mul_const _)) := by
  have hrewardMap : Measurable
      (fun p : (Fin d → ℝ) × ℝ ↦ (p.1, p.1 ⬝ᵥ θ + p.2)) := by
    refine measurable_fst.prodMk ?_
    exact (Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_fst).mul_const _).add
        measurable_snd
  rw [linearStepKernel, Kernel.map_apply _ hrewardMap]
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  change ((π.select k h).compProd
      (Kernel.const (Fin d → ℝ) (gaussianReal 0 1))).map
        (fun p ↦ (p.1, p.1 ⬝ᵥ θ + p.2)) =
    (π.select k h).compProd
      (shiftedGaussianKernel
        (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
        (Finset.measurable_sum _ fun i _ ↦
          (measurable_pi_apply i).mul_const _))
  exact (compProd_shiftedGaussianKernel
    (π.select k h) (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
      (Finset.measurable_sum _ fun i _ ↦
        (measurable_pi_apply i).mul_const _)).symm

private noncomputable def adaptiveLinearMeasure {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    (k : ℕ) → Measure (LinearBanditHistory d k)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | k + 1 =>
      ((adaptiveLinearMeasure θ π k).compProd
        (linearStepKernel θ π)).map
          (fun p ↦ Fin.snoc p.1 p.2)

private instance adaptiveLinearMeasure.instIsProbabilityMeasure {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) (k : ℕ) :
    IsProbabilityMeasure (adaptiveLinearMeasure θ π k) := by
  induction k with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ k ih =>
      rw [adaptiveLinearMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map (by fun_prop)

private theorem linearBanditMeasure_eq_adaptive {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    linearBanditMeasure θ π k = adaptiveLinearMeasure θ π k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [linearBanditMeasure, adaptiveLinearMeasure, ih]
      unfold linearStepKernel
      rw [Measure.compProd_map (by fun_prop)]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rw [← Measure.compProd_assoc']
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply Measure.map_congr
      filter_upwards [] with p
      rfl

private theorem measurable_gaussianPDF_joint
    {α : Type*} [MeasurableSpace α]
    (m : α → ℝ) (hm : Measurable m) :
    Measurable (fun p : α × ℝ ↦ gaussianPDF (m p.1) 1 p.2) := by
  unfold gaussianPDF gaussianPDFReal
  fun_prop

private theorem gaussian_withDensity_ratio (μ ν : ℝ) :
    (gaussianReal ν 1).withDensity
        (fun x ↦ gaussianPDF μ 1 x / gaussianPDF ν 1 x) =
      gaussianReal μ 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    gaussianReal_of_var_ne_zero _ one_ne_zero]
  rw [← withDensity_mul]
  congr 1
  funext x
  exact ENNReal.mul_div_cancel
    (gaussianPDF_pos ν one_ne_zero x).ne'
    gaussianPDF_ne_top
  · exact measurable_gaussianPDF ν 1
  · exact (measurable_gaussianPDF μ 1).div
      (measurable_gaussianPDF ν 1)

private theorem rnDeriv_gaussian_ratio (μ ν : ℝ) :
    (gaussianReal μ 1).rnDeriv (gaussianReal ν 1) =ᵐ[gaussianReal ν 1]
      fun x ↦ gaussianPDF μ 1 x / gaussianPDF ν 1 x := by
  rw [← gaussian_withDensity_ratio μ ν]
  exact Measure.rnDeriv_withDensity _
    ((measurable_gaussianPDF μ 1).div (measurable_gaussianPDF ν 1))

private theorem gaussian_ac (μ ν : ℝ) :
    gaussianReal μ 1 ≪ gaussianReal ν 1 :=
  (gaussianReal_absolutelyContinuous μ one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' ν one_ne_zero)

private noncomputable def gaussianChannelRatio
    {α : Type*} [MeasurableSpace α]
    (m m' : α → ℝ) (p : α × ℝ) : ENNReal :=
  gaussianPDF (m p.1) 1 p.2 / gaussianPDF (m' p.1) 1 p.2

private theorem measurable_gaussianChannelRatio
    {α : Type*} [MeasurableSpace α]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    Measurable (gaussianChannelRatio m m') :=
  (measurable_gaussianPDF_joint m hm).div
    (measurable_gaussianPDF_joint m' hm')

private theorem gaussianChannel_withDensity
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [SFinite ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    (ρ.compProd (shiftedGaussianKernel m' hm')).withDensity
        (gaussianChannelRatio m m') =
      ρ.compProd (shiftedGaussianKernel m hm) := by
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_gaussianChannelRatio m m' hm hm').indicator hs)]
  apply lintegral_congr
  intro a
  rw [shiftedGaussianKernel_apply m' hm' a]
  rw [shiftedGaussianKernel_apply m hm a]
  change (∫⁻ x, s.indicator
      (fun z : α × ℝ ↦ gaussianPDF (m z.1) 1 z.2 /
        gaussianPDF (m' z.1) 1 z.2) (a, x)
      ∂gaussianReal (m' a) 1) =
    gaussianReal (m a) 1 (Prod.mk a ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk a ⁻¹' s,
        gaussianPDF (m a) 1 x / gaussianPDF (m' a) 1 x
        ∂gaussianReal (m' a) 1 := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = ((gaussianReal (m' a) 1).withDensity
          (fun x ↦ gaussianPDF (m a) 1 x /
            gaussianPDF (m' a) 1 x)) (Prod.mk a ⁻¹' s) := by
      rw [withDensity_apply _ (measurable_prodMk_left hs)]
    _ = gaussianReal (m a) 1 (Prod.mk a ⁻¹' s) := by
      rw [gaussian_withDensity_ratio]

private theorem rnDeriv_gaussianChannel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    (ρ.compProd (shiftedGaussianKernel m hm)).rnDeriv
        (ρ.compProd (shiftedGaussianKernel m' hm')) =ᵐ[
      ρ.compProd (shiftedGaussianKernel m' hm')]
        gaussianChannelRatio m m' := by
  rw [← gaussianChannel_withDensity ρ m m' hm hm']
  exact Measure.rnDeriv_withDensity _
    (measurable_gaussianChannelRatio m m' hm hm')

private theorem gaussianChannel_ac
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [SFinite ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    ρ.compProd (shiftedGaussianKernel m hm) ≪
      ρ.compProd (shiftedGaussianKernel m' hm') := by
  rw [← gaussianChannel_withDensity ρ m m' hm hm']
  exact withDensity_absolutelyContinuous _ _

private theorem klDiv_gaussianChannel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    klDiv
        (ρ.compProd (shiftedGaussianKernel m hm))
        (ρ.compProd (shiftedGaussianKernel m' hm')) =
      ∫⁻ a, ENNReal.ofReal ((m a - m' a) ^ 2 / 2) ∂ρ := by
  rw [klDiv_eq_lintegral_klFun_of_ac
    (gaussianChannel_ac ρ m m' hm hm')]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun ((((ρ.compProd (shiftedGaussianKernel m hm)).rnDeriv
          (ρ.compProd (shiftedGaussianKernel m' hm'))) z).toReal))
        ∂ρ.compProd (shiftedGaussianKernel m' hm')) =
      ∫⁻ z, ENNReal.ofReal
        (klFun ((gaussianChannelRatio m m' z).toReal))
        ∂ρ.compProd (shiftedGaussianKernel m' hm') := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_gaussianChannel ρ m m' hm hm'] with z hz
      rw [hz]
    _ = ∫⁻ a, klDiv (gaussianReal (m a) 1)
        (gaussianReal (m' a) 1) ∂ρ := by
      have hmeas : Measurable (fun z : α × ℝ ↦ ENNReal.ofReal
          (klFun ((gaussianChannelRatio m m' z).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp
              (measurable_gaussianChannelRatio m m' hm hm')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr
      intro a
      rw [shiftedGaussianKernel_apply m' hm' a]
      rw [klDiv_eq_lintegral_klFun_of_ac (gaussian_ac (m a) (m' a))]
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_gaussian_ratio (m a) (m' a)] with x hx
      rw [hx]
      rfl
    _ = ∫⁻ a, ENNReal.ofReal ((m a - m' a) ^ 2 / 2) ∂ρ := by
      apply lintegral_congr
      intro a
      simpa using gaussian_relative_entropy_formula (m a) (m' a)
        (v := 1) one_ne_zero

private theorem linearStepKernel_eq_gaussianStep {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    linearStepKernel (k := k) θ π =
      (π.select k).compProd
        (shiftedGaussianKernel
          (fun p : LinearBanditHistory d k × (Fin d → ℝ) ↦
            p.2 ⬝ᵥ θ)
          (by
            exact Finset.measurable_sum _ fun i _ ↦
              ((measurable_pi_apply i).comp measurable_snd).mul_const _)) := by
  ext h s hs
  rw [linearStepKernel_apply θ π h]
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  congr 2
  ext a t ht
  rw [Kernel.sectR_apply]
  rw [shiftedGaussianKernel_apply, shiftedGaussianKernel_apply]

private theorem klDiv_map_embedding
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ η : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure η]
    {f : α → β} (hf : MeasurableEmbedding f) :
    klDiv (μ.map f) (η.map f) = klDiv μ η := by
  by_cases h_ac : μ ≪ η
  · rw [klDiv_eq_lintegral_klFun_of_ac (hf.absolutelyContinuous_map h_ac),
      klDiv_eq_lintegral_klFun_of_ac h_ac]
    rw [hf.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map μ η] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
    intro hmap
    apply h_ac
    intro s hηs
    have hηmap : η.map f (f '' s) = 0 := by
      rw [hf.map_apply, hf.injective.preimage_image]
      exact hηs
    have hμmap := hmap hηmap
    rw [hf.map_apply, hf.injective.preimage_image] at hμmap
    exact hμmap

private theorem klDiv_linearHistorySnoc_map {d k : ℕ}
    (μ η : Measure
      (LinearBanditHistory d k × ((Fin d → ℝ) × ℝ)))
    [IsFiniteMeasure μ] [IsFiniteMeasure η] :
    klDiv
        (μ.map (fun p :
          LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2))
        (η.map (fun p :
          LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2)) =
      klDiv μ η := by
  have hemb : MeasurableEmbedding
      (fun p : LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
        Fin.snoc
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
          p.1 p.2) := by
    apply MeasurableEmbedding.of_measurable_inverse
      (g := fun h : LinearBanditHistory d (k + 1) ↦
        (Fin.init h, h (Fin.last k)))
      (by fun_prop)
    · have hrange : Set.range
          (fun p : LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro h
        exact ⟨(Fin.init h, h (Fin.last k)), Fin.snoc_init_self (q := h)⟩
      rw [hrange]
      exact MeasurableSet.univ
    · fun_prop
    · intro p
      apply Prod.ext
      · exact Fin.init_snoc
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
            (n := k) (p := p.1) (x := p.2)
      · exact Fin.snoc_last
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
            (n := k) (p := p.1) (x := p.2)
  exact klDiv_map_embedding hemb

private theorem klDiv_sameHistory_linearStep {d k : ℕ}
    (M : Measure (LinearBanditHistory d k)) [IsProbabilityMeasure M]
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv
        (M.compProd (linearStepKernel (k := k) θ π))
        (M.compProd (linearStepKernel (k := k) θ' π)) =
      ∫⁻ p : LinearBanditHistory d k × (Fin d → ℝ),
        ENNReal.ofReal
          (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
        ∂M.compProd (π.select k) := by
  rw [linearStepKernel_eq_gaussianStep θ π,
    linearStepKernel_eq_gaussianStep θ' π]
  let m : LinearBanditHistory d k × (Fin d → ℝ) → ℝ :=
    fun p ↦ p.2 ⬝ᵥ θ
  let m' : LinearBanditHistory d k × (Fin d → ℝ) → ℝ :=
    fun p ↦ p.2 ⬝ᵥ θ'
  have hm : Measurable m := by
    exact Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_snd).mul_const _
  have hm' : Measurable m' := by
    exact Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_snd).mul_const _
  have hleft :
      klDiv
        ((M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m hm))).map
            MeasurableEquiv.prodAssoc.symm)
        ((M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m' hm'))).map
            MeasurableEquiv.prodAssoc.symm) =
      klDiv
        (M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m hm)))
        (M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m' hm'))) :=
    klDiv_map_embedding
      (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc.symm)
  rw [Measure.compProd_assoc, Measure.compProd_assoc] at hleft
  rw [← hleft]
  simpa only [m, m'] using
    klDiv_gaussianChannel (M.compProd (π.select k)) m m' hm hm'

private theorem klDiv_adaptiveLinearMeasure_succ {d k : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (adaptiveLinearMeasure θ π (k + 1))
        (adaptiveLinearMeasure θ' π (k + 1)) =
      klDiv (adaptiveLinearMeasure θ π k)
          (adaptiveLinearMeasure θ' π k) +
        ∫⁻ p : LinearBanditHistory d k × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(adaptiveLinearMeasure θ π k).compProd (π.select k) := by
  rw [adaptiveLinearMeasure, adaptiveLinearMeasure]
  rw [klDiv_linearHistorySnoc_map]
  rw [InformationTheory.klDiv_compProd_eq_add]
  congr 1
  exact klDiv_sameHistory_linearStep
    (adaptiveLinearMeasure θ π k) θ θ' π

private theorem klDiv_adaptiveLinearMeasure_eq_sum {d n : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (adaptiveLinearMeasure θ π n)
        (adaptiveLinearMeasure θ' π n) =
      ∑ t ∈ Finset.range n,
        ∫⁻ p : LinearBanditHistory d t × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(adaptiveLinearMeasure θ π t).compProd (π.select t) := by
  induction n with
  | zero =>
      simp [adaptiveLinearMeasure]
  | succ n ih =>
      rw [klDiv_adaptiveLinearMeasure_succ, ih]
      rw [Finset.sum_range_succ]

theorem klDiv_linearBanditMeasure_eq_stage_sum {d n : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (linearBanditMeasure θ π n)
        (linearBanditMeasure θ' π n) =
      ∑ t ∈ Finset.range n,
        ∫⁻ p : LinearBanditHistory d t × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(linearBanditMeasure θ π t).compProd (π.select t) := by
  rw [linearBanditMeasure_eq_adaptive, linearBanditMeasure_eq_adaptive]
  simpa only [← linearBanditMeasure_eq_adaptive] using
    klDiv_adaptiveLinearMeasure_eq_sum θ θ' π

end BanditAlgorithm

open MeasureTheory ProbabilityTheory InformationTheory Matrix BanditAlgorithm

namespace HypercubeLowerBound

theorem measurableSet_cube {d : ℕ} :
    MeasurableSet {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le (measurable_pi_apply i).abs measurable_const

theorem linearBanditStage_action_cube {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π) :
    ∀ᵐ p ∂(linearBanditMeasure θ π t).compProd (π.select t),
      ∀ i, |p.2 i| ≤ 1 := by
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_cube.preimage measurable_snd
  · filter_upwards [] with h
    change {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} ∈ ae (π.select t h)
    rw [mem_ae_iff]
    exact hsupp t h

theorem linearBanditMeasure_allActions_cube {d n : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π) :
    ∀ᵐ h ∂linearBanditMeasure θ π n, ∀ t i, |(h t).1 i| ≤ 1 := by
  induction n with
  | zero =>
      filter_upwards [] with h
      intro t
      exact Fin.elim0 t
  | succ n ih =>
      have hhist : MeasurableSet
          {h : LinearBanditHistory d n | ∀ t i, |(h t).1 i| ≤ 1} := by
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun t =>
          MeasurableSet.iInter fun i => measurableSet_le
            ((measurable_pi_apply i).comp
              (measurable_fst.comp (measurable_pi_apply t))).abs measurable_const
      have hpair :
          ∀ᵐ p ∂(linearBanditMeasure θ π n).compProd (π.select n),
            (∀ t i, |(p.1 t).1 i| ≤ 1) ∧ ∀ i, |p.2 i| ≤ 1 := by
        apply Measure.ae_compProd_of_ae_ae
        · exact (hhist.preimage measurable_fst).inter
            (measurableSet_cube.preimage measurable_snd)
        · filter_upwards [ih] with h hh
          have ha : ∀ᵐ a ∂π.select n h, ∀ i, |a i| ≤ 1 := by
            change {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} ∈ ae (π.select n h)
            rw [mem_ae_iff]
            exact hsupp n h
          filter_upwards [ha] with a ha
          exact ⟨hh, ha⟩
      have htriple :
          ∀ᵐ p ∂((linearBanditMeasure θ π n).compProd (π.select n)).compProd
              (Kernel.const _ (gaussianReal 0 1)),
            (∀ t i, |(p.1.1 t).1 i| ≤ 1) ∧ ∀ i, |p.1.2 i| ≤ 1 :=
        Measure.ae_compProd_of_ae_fst
          (Kernel.const (LinearBanditHistory d n × (Fin d → ℝ)) (gaussianReal 0 1))
          ((hhist.preimage measurable_fst).inter
            (measurableSet_cube.preimage measurable_snd)) hpair
      rw [linearBanditMeasure]
      apply (ae_map_iff (measurable_linearBanditHistorySnoc θ).aemeasurable (by
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun t =>
          MeasurableSet.iInter fun i => measurableSet_le
            ((measurable_pi_apply i).comp
              (measurable_fst.comp (measurable_pi_apply t))).abs measurable_const)).2
      filter_upwards [htriple] with p hp
      intro t i
      refine Fin.lastCases ?_ (fun j => ?_) t
      · simpa using hp.2 i
      · simpa using hp.1 j i

theorem klDiv_le_two_of_coordinate_flip {d n : ℕ} (hn : 0 < n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (θ θ' : Fin d → ℝ) (i : Fin d)
    (hsame : ∀ j, j ≠ i → θ j = θ' j)
    (hgap : (θ i - θ' i) ^ 2 ≤ 4 / (n : ℝ)) :
    klDiv (linearBanditMeasure θ π n) (linearBanditMeasure θ' π n) ≤ 2 := by
  have hdiff (a : Fin d → ℝ) :
      a ⬝ᵥ θ - a ⬝ᵥ θ' = a i * (θ i - θ' i) := by
    simp only [dotProduct]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
    · ring
    · intro j hj hji
      rw [hsame j hji]
      ring
    · simp
  have hstage (t : ℕ) :
      (∫⁻ p : LinearBanditHistory d t × (Fin d → ℝ),
        ENNReal.ofReal (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
        ∂(linearBanditMeasure θ π t).compProd (π.select t)) ≤
          ENNReal.ofReal (2 / (n : ℝ)) := by
    calc
      _ ≤ ∫⁻ _ : LinearBanditHistory d t × (Fin d → ℝ),
          ENNReal.ofReal (2 / (n : ℝ))
          ∂(linearBanditMeasure θ π t).compProd (π.select t) := by
        apply lintegral_mono_ae
        filter_upwards [linearBanditStage_action_cube θ π hsupp] with p hp
        apply ENNReal.ofReal_le_ofReal
        have habs := abs_le.mp (hp i)
        have hsq : p.2 i ^ 2 ≤ 1 := by nlinarith
        have hmul := mul_le_mul hsq hgap (sq_nonneg (θ i - θ' i)) (by norm_num : (0 : ℝ) ≤ 1)
        rw [hdiff, mul_pow]
        calc
          _ ≤ (1 * (4 / (n : ℝ))) / 2 :=
            div_le_div_of_nonneg_right hmul (by norm_num)
          _ = 2 / (n : ℝ) := by ring
      _ = _ := by simp
  rw [BanditAlgorithm.klDiv_linearBanditMeasure_eq_stage_sum]
  calc
    _ ≤ ∑ t ∈ Finset.range n, ENNReal.ofReal (2 / (n : ℝ)) := by
      exact Finset.sum_le_sum fun t _ => hstage t
    _ = 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      have hcancel : (n : ℝ) * (2 / (n : ℝ)) = 2 := by field_simp [hn0]
      rw [hcancel]
      norm_num

end HypercubeLowerBound

open Matrix

namespace HypercubeLowerBound

def sign {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : ℝ :=
  if σ i then 1 else -1

def flip {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : Fin d → Bool :=
  Function.update σ i (!σ i)

noncomputable def delta (n : ℕ) : ℝ := Real.sqrt (1 / (n : ℝ))

noncomputable def theta {d : ℕ} (n : ℕ) (σ : Fin d → Bool) : Fin d → ℝ :=
  fun i ↦ delta n * sign σ i

theorem sign_sq {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    sign σ i ^ 2 = 1 := by
  simp [sign]

theorem abs_sign {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    |sign σ i| = 1 := by
  cases h : σ i <;> simp [sign, h]

theorem sign_flip {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    sign (flip σ i) i = -sign σ i := by
  cases h : σ i <;> simp [sign, flip, h]

theorem flip_involutive {d : ℕ} (i : Fin d) :
    Function.Involutive (fun σ : Fin d → Bool ↦ flip σ i) := by
  intro σ
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

def flipEquiv {d : ℕ} (i : Fin d) : (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun σ := flip σ i
  invFun σ := flip σ i
  left_inv := flip_involutive i
  right_inv := flip_involutive i

theorem sum_flip {d : ℕ} (i : Fin d) (f : (Fin d → Bool) → ℝ) :
    (∑ σ, f (flip σ i)) = ∑ σ, f σ := by
  exact (flipEquiv i).sum_comp f

theorem delta_nonneg (n : ℕ) : 0 ≤ delta n := Real.sqrt_nonneg _

theorem delta_sq (n : ℕ) : delta n ^ 2 = 1 / (n : ℝ) := by
  exact Real.sq_sqrt (by positivity)

theorem theta_flip_other {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (i j : Fin d) (h : j ≠ i) : theta n σ j = theta n (flip σ i) j := by
  simp [theta, sign, flip, h]

theorem theta_flip_gap_sq {d : ℕ} (n : ℕ) (σ : Fin d → Bool) (i : Fin d) :
    (theta n σ i - theta n (flip σ i) i) ^ 2 = 4 / (n : ℝ) := by
  rw [theta, theta, sign_flip]
  calc
    (delta n * sign σ i - delta n * -sign σ i) ^ 2 =
        4 * delta n ^ 2 * sign σ i ^ 2 := by ring
    _ = 4 / (n : ℝ) := by rw [delta_sq, sign_sq]; ring

theorem theta_values {d : ℕ} (n : ℕ) (σ : Fin d → Bool) (i : Fin d) :
    theta n σ i = Real.sqrt (1 / (n : ℝ)) ∨
      theta n σ i = -Real.sqrt (1 / (n : ℝ)) := by
  cases h : σ i <;> simp [theta, sign, delta, h]

theorem sign_mul_coordinate_le_one {d : ℕ} (σ : Fin d → Bool)
    (a : Fin d → ℝ) (ha : ∀ i, |a i| ≤ 1) (i : Fin d) :
    sign σ i * a i ≤ 1 := by
  calc
    sign σ i * a i ≤ |sign σ i * a i| := le_abs_self _
    _ = |a i| := by rw [abs_mul, abs_sign, one_mul]
    _ ≤ 1 := ha i

theorem abs_dot_theta_le {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (a : Fin d → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    |a ⬝ᵥ theta n σ| ≤ (d : ℝ) * delta n := by
  calc
    |a ⬝ᵥ theta n σ| ≤ ∑ i, |a i * theta n σ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, delta n := by
      apply Finset.sum_le_sum
      intro i _
      rw [theta, abs_mul, abs_mul, abs_of_nonneg (delta_nonneg n), abs_sign, mul_one]
      simpa using mul_le_mul_of_nonneg_right (ha i) (delta_nonneg n)
    _ = (d : ℝ) * delta n := by simp

theorem sSup_cube_theta {d : ℕ} (n : ℕ) (σ : Fin d → Bool) :
    sSup ((fun a ↦ a ⬝ᵥ theta n σ) '' {a : Fin d → ℝ | ∀ i, |a i| ≤ 1}) =
      (d : ℝ) * delta n := by
  have hdot : sign σ ⬝ᵥ theta n σ = (d : ℝ) * delta n := by
    calc
      sign σ ⬝ᵥ theta n σ = ∑ _i : Fin d, delta n := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [theta]
        calc
          sign σ i * (delta n * sign σ i) = delta n * sign σ i ^ 2 := by ring
          _ = delta n := by rw [sign_sq, mul_one]
      _ = _ := by simp
  have hmem : (d : ℝ) * delta n ∈
      (fun a ↦ a ⬝ᵥ theta n σ) '' {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} :=
    ⟨sign σ, fun i ↦ (abs_sign σ i).le, hdot⟩
  have hub : ∀ y ∈ (fun a ↦ a ⬝ᵥ theta n σ) ''
      {a : Fin d → ℝ | ∀ i, |a i| ≤ 1}, y ≤ (d : ℝ) * delta n := by
    rintro y ⟨a, ha, rfl⟩
    exact (le_abs_self _).trans (abs_dot_theta_le n σ a ha)
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

noncomputable def coordinateLoss {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (i : Fin d) (a : Fin d → ℝ) : ℝ := delta n * (1 - sign σ i * a i)

theorem coordinateLoss_nonneg {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (i : Fin d) (a : Fin d → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    0 ≤ coordinateLoss n σ i a :=
  mul_nonneg (delta_nonneg n) (sub_nonneg.mpr (sign_mul_coordinate_le_one σ a ha i))

theorem coordinateLoss_le {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (i : Fin d) (a : Fin d → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    coordinateLoss n σ i a ≤ 2 * delta n := by
  have habs : |sign σ i * a i| ≤ 1 := by
    simpa only [abs_mul, abs_sign, one_mul] using ha i
  have hlower := (abs_le.mp habs).1
  have hmul := mul_le_mul_of_nonneg_left (show 1 - sign σ i * a i ≤ 2 by linarith)
    (delta_nonneg n)
  simpa [coordinateLoss, mul_comm] using hmul

theorem coordinateLoss_sum {d : ℕ} (n : ℕ) (σ : Fin d → Bool)
    (a : Fin d → ℝ) :
    (∑ i, coordinateLoss n σ i a) = (d : ℝ) * delta n - a ⬝ᵥ theta n σ := by
  simp only [coordinateLoss, theta, dotProduct, mul_sub, mul_one,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem delta_mul_n {n : ℕ} (hn : 0 < n) : delta n * (n : ℝ) = Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (sq_eq_sq₀ (mul_nonneg (delta_nonneg n) hnR.le) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, delta_sq, Real.sq_sqrt hnR.le]
  field_simp

end HypercubeLowerBound

open Matrix MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace HypercubeLowerBound

def badSignEvent {d n : ℕ} (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    Set (BanditAlgorithm.LinearBanditHistory d n) :=
  {h | sign σ i * (h t).1 i ≤ 0}

open BanditAlgorithm

theorem measurableSet_badSignEvent {d n : ℕ}
    (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    MeasurableSet (badSignEvent σ t i) := by
  exact measurableSet_le
    (measurable_const.mul ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_pi_apply t)))) measurable_const

theorem badSignEvent_compl_subset_flip {d n : ℕ}
    (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    (badSignEvent σ t i)ᶜ ⊆ badSignEvent (flip σ i) t i := by
  intro h hh
  change ¬sign σ i * (h t).1 i ≤ 0 at hh
  change sign (flip σ i) i * (h t).1 i ≤ 0
  rw [sign_flip]
  linarith

theorem badSign_pair_lower {d n : ℕ} (hn : 0 < n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    Real.exp (-2) / 2 ≤
      (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i) +
        (linearBanditMeasure (theta n (flip σ i)) π n).real
          (badSignEvent (flip σ i) t i) := by
  have hD := klDiv_le_two_of_coordinate_flip hn π hsupp
    (theta n σ) (theta n (flip σ i)) i
    (fun j hj ↦ theta_flip_other n σ i j hj) (theta_flip_gap_sq n σ i).le
  have hfinite : klDiv (linearBanditMeasure (theta n σ) π n)
      (linearBanditMeasure (theta n (flip σ i)) π n) ≠ ∞ :=
    ne_of_lt (hD.trans_lt (by norm_num))
  have hreal : (klDiv (linearBanditMeasure (theta n σ) π n)
      (linearBanditMeasure (theta n (flip σ i)) π n)).toReal ≤ 2 := by
    exact_mod_cast ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hD
  have hBH := bretagnolle_huber_inequality
    (linearBanditMeasure (theta n σ) π n)
    (linearBanditMeasure (theta n (flip σ i)) π n)
    (measurableSet_badSignEvent σ t i) hfinite
  have hexp := Real.exp_le_exp.mpr (neg_le_neg hreal)
  have hset := measureReal_mono (μ := linearBanditMeasure (theta n (flip σ i)) π n)
    (badSignEvent_compl_subset_flip σ t i)
  linarith

theorem badSign_cube_sum_lower {d n : ℕ} (hn : 0 < n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (t : Fin n) (i : Fin d) :
    (Fintype.card (Fin d → Bool) : ℝ) * (Real.exp (-2) / 4) ≤
      ∑ σ : Fin d → Bool,
        (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun σ _ ↦ badSign_pair_lower hn π hsupp σ t i)
  rw [Finset.sum_add_distrib,
    sum_flip i (fun σ ↦ (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i))] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  linarith

theorem integrable_coordinateLoss {d n : ℕ} (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    Integrable (fun h : LinearBanditHistory d n ↦ coordinateLoss n σ i (h t).1)
      (linearBanditMeasure (theta n σ) π n) := by
  have hm : Measurable (fun h : LinearBanditHistory d n ↦ coordinateLoss n σ i (h t).1) := by
    unfold coordinateLoss
    fun_prop
  apply Integrable.of_bound hm.aestronglyMeasurable (2 * delta n)
  filter_upwards [linearBanditMeasure_allActions_cube (theta n σ) π hsupp] with h hh
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateLoss_nonneg n σ i _ (hh t))]
  exact coordinateLoss_le n σ i _ (hh t)

theorem expectedRegret_eq_coordinateLoss {d n : ℕ} (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (σ : Fin d → Bool) :
    linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} (theta n σ) π n =
      ∑ t : Fin n, ∑ i : Fin d,
        ∫ h, coordinateLoss n σ i (h t).1 ∂linearBanditMeasure (theta n σ) π n := by
  have hint (t : Fin n) : Integrable
      (fun h : LinearBanditHistory d n ↦ ∑ i : Fin d, coordinateLoss n σ i (h t).1)
      (linearBanditMeasure (theta n σ) π n) :=
    integrable_finsetSum _ (fun i _ ↦ integrable_coordinateLoss π hsupp σ t i)
  have htotal : Integrable
      (fun h : LinearBanditHistory d n ↦ ∑ t : Fin n, ∑ i : Fin d,
        coordinateLoss n σ i (h t).1) (linearBanditMeasure (theta n σ) π n) :=
    integrable_finsetSum _ (fun t _ ↦ hint t)
  have hidentity : (fun h : LinearBanditHistory d n ↦ ∑ t, (h t).1 ⬝ᵥ theta n σ) =
      fun h ↦ (n : ℝ) * ((d : ℝ) * delta n) -
        ∑ t : Fin n, ∑ i : Fin d, coordinateLoss n σ i (h t).1 := by
    funext h
    simp_rw [coordinateLoss_sum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [linearBanditExpectedRegret, sSup_cube_theta, hidentity,
    integral_sub (integrable_const _) htotal]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_sub_cancel]
  rw [integral_finsetSum _ (fun t _ ↦ hint t)]
  apply Finset.sum_congr rfl
  intro t _
  exact integral_finsetSum _ (fun i _ ↦ integrable_coordinateLoss π hsupp σ t i)

theorem coordinateLoss_integral_lower {d n : ℕ} (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (σ : Fin d → Bool) (t : Fin n) (i : Fin d) :
    delta n * (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i) ≤
      ∫ h, coordinateLoss n σ i (h t).1 ∂linearBanditMeasure (theta n σ) π n := by
  have hmeas := measurableSet_badSignEvent σ t i
  have h := integral_mono_ae
    ((integrable_const (delta n)).indicator hmeas)
    (integrable_coordinateLoss π hsupp σ t i) ?_
  · simpa only [integral_indicator_const _ hmeas, smul_eq_mul, mul_comm] using h
  filter_upwards [linearBanditMeasure_allActions_cube (theta n σ) π hsupp] with h hh
  by_cases hb : h ∈ badSignEvent σ t i
  · rw [Set.indicator_of_mem hb]
    change sign σ i * (h t).1 i ≤ 0 at hb
    dsimp [coordinateLoss]
    have := mul_nonpos_of_nonneg_of_nonpos (delta_nonneg n) hb
    nlinarith
  · rw [Set.indicator_of_notMem hb]
    exact coordinateLoss_nonneg n σ i _ (hh t)

theorem expectedRegret_badSign_lower {d n : ℕ} (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π)
    (σ : Fin d → Bool) :
    delta n * (∑ t : Fin n, ∑ i : Fin d,
      (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i)) ≤
      linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} (theta n σ) π n := by
  rw [expectedRegret_eq_coordinateLoss π hsupp σ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro i _
  exact coordinateLoss_integral_lower π hsupp σ t i

theorem cube_average_regret_lower {d n : ℕ} (hn : 0 < n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π) :
    (Fintype.card (Fin d → Bool) : ℝ) * (Real.exp (-2) / 4 * ((d : ℝ) * Real.sqrt n)) ≤
      ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} (theta n σ) π n := by
  let f := fun (σ : Fin d → Bool) (t : Fin n) (i : Fin d) ↦
    (linearBanditMeasure (theta n σ) π n).real (badSignEvent σ t i)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun σ _ ↦ expectedRegret_badSign_lower (n := n) π hsupp σ)
  rw [← Finset.mul_sum] at hsum
  have hswap : (∑ σ : Fin d → Bool, ∑ t : Fin n, ∑ i : Fin d, f σ t i) =
      ∑ t : Fin n, ∑ i : Fin d, ∑ σ : Fin d → Bool, f σ t i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    exact Finset.sum_comm
  change delta n * (∑ σ : Fin d → Bool, ∑ t : Fin n, ∑ i : Fin d, f σ t i) ≤ _ at hsum
  rw [hswap] at hsum
  have havg : (∑ t : Fin n, ∑ i : Fin d,
      (Fintype.card (Fin d → Bool) : ℝ) * (Real.exp (-2) / 4)) ≤
      ∑ t : Fin n, ∑ i : Fin d, ∑ σ : Fin d → Bool, f σ t i := by
    apply Finset.sum_le_sum
    intro t _
    apply Finset.sum_le_sum
    intro i _
    exact badSign_cube_sum_lower hn π hsupp t i
  have h := (mul_le_mul_of_nonneg_left havg (delta_nonneg n)).trans hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  rw [show delta n * ((n : ℝ) * ((d : ℝ) *
      ((Fintype.card (Fin d → Bool) : ℝ) * (Real.exp (-2) / 4)))) =
      (Fintype.card (Fin d → Bool) : ℝ) *
        (Real.exp (-2) / 4 * ((d : ℝ) * (delta n * n))) by ring,
    delta_mul_n hn]

end HypercubeLowerBound

open BanditAlgorithm HypercubeLowerBound

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} π) :
    ∃ θ : Fin d → ℝ,
      (∀ i, θ i = Real.sqrt (1 / n) ∨ θ i = -Real.sqrt (1 / n)) ∧
      Real.exp (-2) / 8 * (d * Real.sqrt n) ≤
        linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} θ π n := by
  have havg := cube_average_regret_lower hn π hsupp
  have hweak : (∑ _σ : Fin d → Bool, Real.exp (-2) / 8 * ((d : ℝ) * Real.sqrt n)) ≤
      ∑ σ : Fin d → Bool,
        linearBanditExpectedRegret {a : Fin d → ℝ | ∀ i, |a i| ≤ 1} (theta n σ) π n := by
    refine le_trans ?_ havg
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    gcongr
    norm_num
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hweak
  exact ⟨theta n σ, theta_values n σ, hσ⟩

#print axioms solution
