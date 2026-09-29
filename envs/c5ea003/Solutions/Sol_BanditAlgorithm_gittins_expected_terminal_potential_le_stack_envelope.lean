-- Prove2me | solution 1 for BanditAlgorithm.gittins_expected_terminal_potential_le_stack_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:12:12.517431+00:00
-- url     : https://prove2.me/submissions/5a3401ee-d2de-4c04-b10b-e70c9d52b279

import Definitions.Def_GittinsChargeInterleaving
import Definitions.Def_GittinsFiniteRetirementValue
import Definitions.Def_GittinsIndex
import Definitions.Def_MarkovChainKernel
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.MetricSpace.Bounded
import Theorems.Thm_BanditAlgorithm_gittinsFiniteRetirementValue_mono_of_integrable
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_bellman_of_finite_tendsto
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_iff_index_le
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_lipschitz_charge
import Theorems.Thm_BanditAlgorithm_gittins_stopping_ratio_le_index
import Theorems.Thm_BanditAlgorithm_integrable_discountedStoppedSum
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_one_bounds
import Theorems.Thm_BanditAlgorithm_integral_discountedStoppedSum_sub_charge
import Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
import Theorems.Thm_BanditAlgorithm_measurable_gittinsRetirementValue_of_finite_tendsto


import Definitions.Def_GittinsTerminalPotential
import Definitions.Def_GittinsPrevailingChargeValue
import Theorems.Thm_BanditAlgorithm_gittins_current_terminal_potential_le_stack_envelope
import Theorems.Thm_BanditAlgorithm_gittins_terminal_potential_regular
open MeasureTheory ProbabilityTheory
open Filter Topology

namespace BanditAlgorithm

noncomputable def finiteRetirementSegment
    {S : Type*} (α : ℝ) (q : S → ℝ)
    (b m : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ j ∈ Finset.range m, α ^ j * q (ω (b + j))

lemma discountedStoppedSum_coe_nat
    {S : Type*} (α : ℝ) (f : S → ℝ)
    (m : (ℕ → S) → ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun z ↦ (m z : ℕ∞)) ω =
      finiteRetirementSegment α f 0 (m ω) ω := by
  rw [discountedStoppedSum, finiteRetirementSegment,
    tsum_eq_sum (s := Finset.range (m ω))]
  · apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_range] at ht
    simp [ht]
  · intro t ht
    simp only [Finset.mem_range, not_lt] at ht
    simp [not_lt_of_ge ht]

lemma markovChainMeasure_eq_traj_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainMeasure P x =
      Kernel.traj (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦ x) := by
  rw [← markovChainKernel_apply, markovChainKernel, Kernel.comap_apply]

noncomputable def trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) : Measure S :=
  (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀).map
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)

lemma trajectoryStateMarginal_zero
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b 0 x₀ =
      Measure.dirac (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  simp only [trajectoryStateMarginal, Nat.add_zero,
    Kernel.partialTraj_self, Kernel.id_apply]
  rw [Measure.map_dirac' (by fun_prop)]

private lemma map_bind_kernel
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B) (hf : Measurable f)
    (K : Kernel B C) :
    (μ.map f).bind K = μ.bind (fun x ↦ K (f x)) := by
  rw [Measure.bind, Measure.bind, Measure.map_map]
  · rfl
  · exact K.measurable
  · exact hf

lemma trajectoryStateMarginal_succ
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b (t + 1) x₀ =
      (trajectoryStateMarginal P b t x₀).bind P := by
  rw [trajectoryStateMarginal, trajectoryStateMarginal]
  simp only [Nat.add_succ]
  rw [← Kernel.map_apply _ (by fun_prop)]
  rw [Kernel.partialTraj_succ_eq_comp (by omega : b ≤ b + t)]
  rw [Kernel.map_comp]
  rw [Kernel.map_partialTraj_succ_self]
  rw [Kernel.comp_apply]
  rw [markovChainStep]
  rw [map_bind_kernel
    (Kernel.partialTraj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b (b + t) x₀)
    (fun z ↦ z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩)
    (by fun_prop) P]
  apply Measure.bind_congr_right
  filter_upwards with z
  rw [Kernel.comap_apply]

lemma trajectoryStateMarginal_eq_from_current
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    trajectoryStateMarginal P b t x₀ =
      trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  induction t with
  | zero =>
      rw [trajectoryStateMarginal_zero, trajectoryStateMarginal_zero]
  | succ t ih =>
      rw [trajectoryStateMarginal_succ,
        trajectoryStateMarginal_succ, ih]

lemma map_traj_eval_eq_trajectoryStateMarginal
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      trajectoryStateMarginal P b t x₀ := by
  rw [trajectoryStateMarginal]
  rw [show (fun ω : ℕ → S ↦ ω (b + t)) =
      (fun z : (j : Finset.Iic (b + t)) → S ↦
        z ⟨b + t, Finset.mem_Iic.2 le_rfl⟩) ∘
      Preorder.frestrictLe (π := fun _ : ℕ ↦ S) (b + t) by rfl]
  rw [← Measure.map_map]
  · have hproj :=
      Kernel.traj_map_frestrictLe_apply
        (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
        b (b + t) x₀
    rw [hproj]
  · fun_prop
  · fun_prop

lemma map_traj_eval_eq_map_markovChainMeasure_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) b x₀).map
        (fun ω ↦ ω (b + t)) =
      (markovChainMeasure P
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
  rw [markovChainMeasure_eq_traj_zero]
  calc
    (Kernel.traj (X := fun _ : ℕ ↦ S)
        (markovChainStep P) b x₀).map (fun ω ↦ ω (b + t)) =
        trajectoryStateMarginal P b t x₀ :=
      map_traj_eval_eq_trajectoryStateMarginal P b t x₀
    _ = trajectoryStateMarginal P 0 t
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      trajectoryStateMarginal_eq_from_current P b t x₀
    _ = (Kernel.traj (X := fun _ : ℕ ↦ S) (markovChainStep P) 0
        (fun _ : Finset.Iic 0 ↦
          x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun ω ↦ ω t) := by
      simpa using
        (map_traj_eval_eq_trajectoryStateMarginal P 0 t
          (fun _ : Finset.Iic 0 ↦
            x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).symm

lemma constNat_isTrajStoppingTime
    {S : Type*} [MeasurableSpace S] (m : ℕ) :
    IsTrajStoppingTime (fun _ : ℕ → S ↦ (m : ℕ∞)) := by
  intro t
  by_cases hmt : m ≤ t
  · convert MeasurableSet.univ
    ext ω
    simp [hmt]
  · convert MeasurableSet.empty
    ext ω
    simp [hmt]

lemma discountedStoppedSum_const_succ
    {S : Type*} (α : ℝ) (f : S → ℝ) (n : ℕ) (ω : ℕ → S) :
    discountedStoppedSum α f (fun _ ↦ ((n + 1 : ℕ) : ℕ∞)) ω =
      discountedStoppedSum α f (fun _ ↦ (n : ℕ∞)) ω +
        α ^ n * f (ω n) := by
  rw [discountedStoppedSum_coe_nat,
    discountedStoppedSum_coe_nat,
    finiteRetirementSegment, finiteRetirementSegment]
  rw [Finset.sum_range_succ]
  simp

lemma integrable_markovChain_eval_of_discounted
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (t : ℕ) :
    Integrable (fun ω : ℕ → S ↦ r (ω t))
      (markovChainMeasure P x) := by
  have hsucc := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) (t + 1))
  have hprev := integrable_discountedStoppedSum P hr hα0.le hint x
    (constNat_isTrajStoppingTime (S := S) t)
  have hdiff := hsucc.sub hprev
  have heq :
      (fun ω : ℕ → S ↦
        discountedStoppedSum α r
            (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
          discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω) =
        fun ω ↦ α ^ t * r (ω t) := by
    funext ω
    rw [discountedStoppedSum_const_succ]
    ring
  change Integrable (fun ω : ℕ → S ↦
      discountedStoppedSum α r
          (fun _ ↦ ((t + 1 : ℕ) : ℕ∞)) ω -
        discountedStoppedSum α r (fun _ ↦ (t : ℕ∞)) ω)
      (markovChainMeasure P x) at hdiff
  rw [heq] at hdiff
  have hscaled := hdiff.const_mul (α ^ t)⁻¹
  simpa [mul_assoc, pow_ne_zero t hα0.ne'] using hscaled

private lemma measurable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.mul
    (by
      have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
        hr.comp (measurable_pi_apply t)
      fun_prop)

private lemma measurable_discountedAbsSeriesENNReal
    {S : Type*} [MeasurableSpace S] {α : ℝ}
    {r : S → ℝ} (hr : Measurable r) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) := by
  apply Measurable.ennreal_tsum
  intro t
  exact ENNReal.measurable_ofReal.comp
    (measurable_const.mul
      (by
        have ht : Measurable (fun ω : ℕ → S ↦ r (ω t)) :=
          hr.comp (measurable_pi_apply t)
        fun_prop))

private lemma ae_summable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    ∀ᵐ ω ∂markovChainMeasure P x,
      Summable (fun t : ℕ ↦ α ^ t * |r (ω t)|) := by
  have hfinite :
      ∀ᵐ ω ∂markovChainMeasure P x,
        (∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)) < ⊤ :=
    ae_lt_top (measurable_discountedAbsSeriesENNReal hr)
      (ne_of_lt (hint x))
  filter_upwards [hfinite] with ω hω
  have hs := ENNReal.summable_toReal (ne_of_lt hω)
  simpa [ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs

private lemma integrable_discountedAbsSeries
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α) (x : S) :
    Integrable (fun ω : ℕ → S ↦
      ∑' t : ℕ, α ^ t * |r (ω t)|)
      (markovChainMeasure P x) := by
  refine ⟨(measurable_discountedAbsSeries hr).aestronglyMeasurable, ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂markovChainMeasure P x,
        0 ≤ ∑' t : ℕ, α ^ t * |r (ω t)| :=
    Filter.Eventually.of_forall fun ω ↦ tsum_nonneg fun t ↦
      mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal (∑' t : ℕ, α ^ t * |r (ω t)|)
        ∂markovChainMeasure P x) =
        ∫⁻ ω, ∑' t : ℕ, ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P x := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries P hr hα0 hint x]
        with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦ mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hint x

noncomputable def discountedAbsoluteRewardValue
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ) (x : S) : ℝ :=
  ∫ ω, ∑' t : ℕ, α ^ t * |r (ω t)|
    ∂markovChainMeasure P x

noncomputable def discountedAbsoluteRewardFuture
    {S : Type*} (r : S → ℝ) (α : ℝ)
    (b : ℕ) (ω : ℕ → S) : ℝ :=
  ∑' t : ℕ, α ^ t * |r (ω (b + t))|

private lemma measurable_discountedAbsoluteRewardFuture
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (discountedAbsoluteRewardFuture r α b) := by
  apply Measurable.tsum
  intro t
  fun_prop

private lemma measurable_discountedAbsoluteRewardFutureENNReal
    {S : Type*} [MeasurableSpace S]
    {r : S → ℝ} (hr : Measurable r) (α : ℝ) (b : ℕ) :
    Measurable (fun ω : ℕ → S ↦
      ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) := by
  apply Measurable.ennreal_tsum
  intro t
  fun_prop

lemma lintegral_traj_eval_eq_markovChain_eval
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (f : S → ENNReal) (hf : Measurable f)
    (b t : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), f (ω (b + t))
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), f (ω t)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  have hleft :
      (∫⁻ y, f y ∂
        ((Kernel.traj (markovChainStep P) b x₀).map
          (fun ω : ℕ → S ↦ ω (b + t)))) =
        ∫⁻ (ω : ℕ → S), f (ω (b + t))
          ∂Kernel.traj (markovChainStep P) b x₀ :=
    MeasureTheory.lintegral_map
      hf (measurable_pi_apply (b + t))
  have hright :
      (∫⁻ y, f y ∂
        ((markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)).map
            (fun ω : ℕ → S ↦ ω t))) =
        ∫⁻ (ω : ℕ → S), f (ω t)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
    MeasureTheory.lintegral_map hf (measurable_pi_apply t)
  rw [map_traj_eval_eq_map_markovChainMeasure_eval P b t x₀] at hleft
  exact hleft.symm.trans hright

lemma lintegral_discountedAbsoluteRewardFutureENNReal_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α : ℝ) (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
      ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω t)|)
        ∂markovChainMeasure P
          (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  calc
    (∫⁻ (ω : ℕ → S), ∑' t : ℕ,
        ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
        ∂Kernel.traj (markovChainStep P) b x₀) =
        ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)
          ∂Kernel.traj (markovChainStep P) b x₀ :=
      MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|))).aemeasurable)
    _ = ∑' t : ℕ, ∫⁻ (ω : ℕ → S),
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
      apply tsum_congr
      intro t
      exact lintegral_traj_eval_eq_markovChain_eval
        P (fun y ↦ ENNReal.ofReal (α ^ t * |r y|))
        (by fun_prop) b t x₀
    _ = ∫⁻ (ω : ℕ → S), ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P
            (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) :=
      (MeasureTheory.lintegral_tsum
        (fun t ↦ (by fun_prop :
          Measurable (fun ω : ℕ → S ↦
            ENNReal.ofReal
              (α ^ t * |r (ω t)|))).aemeasurable)).symm

lemma integrable_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    Integrable (discountedAbsoluteRewardFuture r α b)
      (Kernel.traj (markovChainStep P) b x₀) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩)
  have hfinite :
      ∀ᵐ ω ∂μ,
        (∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|)) < ⊤ :=
    ae_lt_top
      (measurable_discountedAbsoluteRewardFutureENNReal
        hr α b) (ne_of_lt hlin)
  have hsummable :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  refine ⟨
    (measurable_discountedAbsoluteRewardFuture
      hr α b).aestronglyMeasurable,
    ?_⟩
  have hnonneg :
      ∀ᵐ ω ∂μ,
        0 ≤ discountedAbsoluteRewardFuture r α b ω :=
    Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  rw [hasFiniteIntegral_iff_ofReal hnonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsummable] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ < ⊤ := hlin

theorem integral_discountedAbsoluteRewardFuture_traj
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 ≤ α)
    (hint : DiscountedRewardIntegrable P r α)
    (b : ℕ) (x₀ : (j : Finset.Iic b) → S) :
    (∫ ω, discountedAbsoluteRewardFuture r α b ω
        ∂Kernel.traj (markovChainStep P) b x₀) =
      discountedAbsoluteRewardValue P r α
        (x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩) := by
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) b x₀
  let y := x₀ ⟨b, Finset.mem_Iic.2 le_rfl⟩
  have hleft :=
    integrable_discountedAbsoluteRewardFuture_traj
      P hr hα0 hint b x₀
  have hright :=
    integrable_discountedAbsSeries P hr hα0 hint y
  have hleft0 :
      0 ≤ ∫ ω, discountedAbsoluteRewardFuture r α b ω ∂μ :=
    integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  have hright0 :
      0 ≤ discountedAbsoluteRewardValue P r α y := by
    dsimp [discountedAbsoluteRewardValue]
    exact integral_nonneg fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)
  apply (ENNReal.ofReal_eq_ofReal_iff hleft0 hright0).mp
  dsimp [discountedAbsoluteRewardValue]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hleft (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    hright (Filter.Eventually.of_forall fun ω ↦
      tsum_nonneg fun t ↦
        mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _))]
  change
    (∫⁻ ω, ENNReal.ofReal
      (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
    ∫⁻ ω, ENNReal.ofReal
      (∑' t : ℕ, α ^ t * |r (ω t)|)
      ∂markovChainMeasure P y
  have hlin :
      (∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ) < ⊤ := by
    rw [lintegral_discountedAbsoluteRewardFutureENNReal_traj
      P hr α b x₀]
    exact hint y
  have hleftsum :
      ∀ᵐ ω ∂μ,
        Summable (fun t : ℕ ↦
          α ^ t * |r (ω (b + t))|) := by
    have hfinite :
        ∀ᵐ ω ∂μ,
          (∑' t : ℕ,
            ENNReal.ofReal
              (α ^ t * |r (ω (b + t))|)) < ⊤ :=
      ae_lt_top
        (measurable_discountedAbsoluteRewardFutureENNReal
          hr α b) (ne_of_lt hlin)
    filter_upwards [hfinite] with ω hω
    have hs := ENNReal.summable_toReal (ne_of_lt hω)
    simpa [ENNReal.toReal_ofReal
      (mul_nonneg (pow_nonneg hα0 _) (abs_nonneg _))] using hs
  calc
    (∫⁻ ω, ENNReal.ofReal
        (discountedAbsoluteRewardFuture r α b ω) ∂μ) =
        ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω (b + t))|) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hleftsum] with ω hω
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω
    _ = ∫⁻ ω, ∑' t : ℕ,
          ENNReal.ofReal (α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y :=
      lintegral_discountedAbsoluteRewardFutureENNReal_traj
        P hr α b x₀
    _ = ∫⁻ ω, ENNReal.ofReal
          (∑' t : ℕ, α ^ t * |r (ω t)|)
          ∂markovChainMeasure P y := by
      apply lintegral_congr_ae
      filter_upwards
        [ae_summable_discountedAbsSeries
          P hr hα0 hint y] with ω hω
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun t ↦
          mul_nonneg (pow_nonneg hα0 t) (abs_nonneg _)) hω).symm

lemma integrable_discountedAbsoluteRewardFuture_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable (discountedAbsoluteRewardFuture r α N)
      (markovChainMeasure P x) := by
  let R : (ℕ → S) → ℝ :=
    fun ω ↦ ∑' t : ℕ, α ^ t * |r (ω t)|
  let Q : (ℕ → S) → ℝ :=
    fun ω ↦ ∑ t ∈ Finset.range N, α ^ t * |r (ω t)|
  have hR : Integrable R (markovChainMeasure P x) :=
    integrable_discountedAbsSeries P hr hα0.le hint x
  have hQ : Integrable Q (markovChainMeasure P x) := by
    apply MeasureTheory.integrable_finset_sum
    intro t ht
    exact (integrable_markovChain_eval_of_discounted
      P hr hα0 hint x t).norm.const_mul (α ^ t)
  have hdiff := hR.sub hQ
  have heq :
      (fun ω ↦ R ω - Q ω) =ᵐ[markovChainMeasure P x]
        fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω := by
    filter_upwards
      [ae_summable_discountedAbsSeries
        P hr hα0.le hint x] with ω hs
    have hsplit := hs.sum_add_tsum_nat_add N
    dsimp [R, Q, discountedAbsoluteRewardFuture]
    rw [← hsplit]
    simp only [add_sub_cancel_left]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro t
    rw [pow_add]
    rw [Nat.add_comm t N]
    ring
  have hscaledInt :
      Integrable
        (fun ω ↦ α ^ N *
          discountedAbsoluteRewardFuture r α N ω)
        (markovChainMeasure P x) :=
    hdiff.congr heq
  have hscaled := hscaledInt.const_mul (α ^ N)⁻¹
  simpa [mul_assoc, pow_ne_zero N hα0.ne'] using hscaled

set_option maxHeartbeats 800000 in
theorem integrable_discountedAbsoluteRewardValue_along_markov
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (N : ℕ) :
    Integrable
      (fun ω : ℕ → S ↦
        discountedAbsoluteRewardValue P r α (ω N))
      (markovChainMeasure P x) ∧
    (∫ ω, discountedAbsoluteRewardValue P r α (ω N)
        ∂markovChainMeasure P x) =
      ∫ ω, discountedAbsoluteRewardFuture r α N ω
        ∂markovChainMeasure P x := by
  let x₀ : (j : Finset.Iic 0) → S := fun _ ↦ x
  let μ :=
    Kernel.traj (X := fun _ : ℕ ↦ S)
      (markovChainStep P) 0 x₀
  let F : (ℕ → S) → ℝ :=
    discountedAbsoluteRewardFuture r α N
  have hFmarkov :
      Integrable F (markovChainMeasure P x) :=
    integrable_discountedAbsoluteRewardFuture_markov
      P hr hα0 hint x N
  have hmeasure : markovChainMeasure P x = μ := by
    rw [markovChainMeasure_eq_traj_zero]
  have hF : Integrable F μ := by
    rwa [← hmeasure]
  have hcond :=
    Kernel.condExp_traj
      (X := fun _ : ℕ ↦ S) (κ := markovChainStep P)
      (a := 0) (b := N) (Nat.zero_le N)
      (x₀ := x₀) hF
  let C : (ℕ → S) → ℝ :=
    MeasureTheory.condExp
      (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
      μ F
  have hCint : Integrable C μ := integrable_condExp
  have heq :
      C =ᵐ[μ] fun ω ↦
        discountedAbsoluteRewardValue P r α (ω N) := by
    filter_upwards [hcond] with ω hω
    change
      MeasureTheory.condExp
        (Filtration.piLE (X := fun _ : ℕ ↦ S) N)
        μ F ω =
        discountedAbsoluteRewardValue P r α (ω N)
    rw [hω]
    simpa [F] using
      (integral_discountedAbsoluteRewardFuture_traj
        P hr hα0.le hint N (Preorder.frestrictLe N ω))
  have hAintμ :
      Integrable
        (fun ω : ℕ → S ↦
          discountedAbsoluteRewardValue P r α (ω N)) μ :=
    hCint.congr heq
  have hintEqμ :
      (∫ ω, discountedAbsoluteRewardValue P r α (ω N) ∂μ) =
        ∫ ω, F ω ∂μ := by
    rw [← integral_congr_ae heq]
    exact integral_condExp
      (Filtration.le
        (Filtration.piLE (X := fun _ : ℕ ↦ S)) N)
  constructor
  · rw [hmeasure]
    exact hAintμ
  · rw [hmeasure]
    simpa [F] using hintEqμ

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



@[simp] lemma currentHistoryPrevailingCharge_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (h : MarkovBanditHistory k S 0) (i : Fin k) :
    currentHistoryPrevailingCharge g 0 h i = g (h.2 i) :=
  rfl

end BanditAlgorithm

namespace BanditAlgorithm




@[simp] lemma stackPullCountBefore_zero
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) :
    stackPullCountBefore a i 0 = 0 := by
  simp [stackPullCountBefore]

lemma stackPullCountBefore_succ
    {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) :
    stackPullCountBefore a i (n + 1) =
      stackPullCountBefore a i n + if a n = i then 1 else 0 := by
  rw [stackPullCountBefore, stackPullCountBefore,
    Finset.sum_range_succ]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




def markovBanditStackHistory
    {k n : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ ω i (stackPullCountBefore a i t), a t),
    fun i ↦ ω i (stackPullCountBefore a i n))

@[simp] lemma markovBanditStackHistory_zero
    {k : ℕ} {S : Type*}
    (ω : Fin k → ℕ → S) (a : ℕ → Fin k) :
    markovBanditStackHistory (n := 0) ω a =
      (fun t ↦ t.elim0, fun i ↦ ω i 0) := by
  apply Prod.ext
  · funext t
    exact Fin.elim0 t
  · funext i
    simp [markovBanditStackHistory]

noncomputable def markovBanditArmPrevailingChargeStack
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) : ℝ :=
  (Finset.range (u + 1)).inf'
    ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
    (fun v ↦ g (ω i v))

@[simp] lemma markovBanditArmPrevailingChargeStack_zero
    {k : ℕ} {S : Type*} (g : S → ℝ)
    (ω : Fin k → ℕ → S) (i : Fin k) :
    markovBanditArmPrevailingChargeStack g ω i 0 = g (ω i 0) := by
  simp [markovBanditArmPrevailingChargeStack]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm



abbrev MarkovBanditStackSpace (k : ℕ) (S : Type*) :=
  Fin k → ℕ → S


noncomputable def markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) : Measure (MarkovBanditStackSpace k S) :=
  Measure.pi (fun i ↦ markovChainMeasure P (x i))

instance markovBanditStackMeasure.instIsProbabilityMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) :
    IsProbabilityMeasure (markovBanditStackMeasure P x) := by
  rw [markovBanditStackMeasure]
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [markovChainMeasure]
    infer_instance
  exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _

theorem map_markovBanditStackMeasure_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (i : Fin k) :
    (markovBanditStackMeasure P x).map (fun omega ↦ omega i) =
      markovChainMeasure P (x i) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  rw [markovBanditStackMeasure, Measure.pi_map_eval]
  simp


def finiteStackPullCountBefore
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k) (t : ℕ) : ℕ :=
  ∑ s : Fin n, if (s : ℕ) < t ∧ a s = i then 1 else 0

@[simp] lemma finiteStackPullCountBefore_restrict
    {k n : ℕ} (a : ℕ → Fin k) (i : Fin k) (t : ℕ)
    (ht : t ≤ n) :
    finiteStackPullCountBefore (fun s : Fin n ↦ a s) i t =
      stackPullCountBefore a i t := by
  classical
  rw [finiteStackPullCountBefore, stackPullCountBefore]
  rw [Fin.sum_univ_eq_sum_range
    (fun s : ℕ ↦ if s < t ∧ a s = i then 1 else 0) n]
  have hsubset : Finset.range t ⊆ Finset.range n := Finset.range_mono ht
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro s hs
    simp [Finset.mem_range.1 hs]
  · intro s hsn hst
    have hts : t ≤ s := by
      simpa [Finset.mem_range] using hst
    simp [not_lt_of_ge hts]


def markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ omega i (finiteStackPullCountBefore a i t), a t),
    fun i ↦ omega i (finiteStackPullCountBefore a i n))

lemma measurable_markovBanditFiniteStackHistory
    {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (fun p : MarkovBanditStackSpace k S × (Fin n → Fin k) ↦
      markovBanditFiniteStackHistory p.1 p.2) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro t
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      change Measurable (fun p : MarkovBanditStackSpace k S ×
        (Fin n → Fin k) ↦ p.1 i (finiteStackPullCountBefore p.2 i t))
      exact measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply (finiteStackPullCountBefore a i t)).comp
          (measurable_pi_apply i)
    · exact (measurable_pi_apply t).comp measurable_snd
  · rw [measurable_pi_iff]
    intro i
    change Measurable (fun p : MarkovBanditStackSpace k S ×
      (Fin n → Fin k) ↦ p.1 i (finiteStackPullCountBefore p.2 i n))
    exact measurable_from_prod_countable_left fun a ↦
      (measurable_pi_apply (finiteStackPullCountBefore a i n)).comp
        (measurable_pi_apply i)

set_option maxHeartbeats 800000 in
lemma map_eval_zero_trajMeasure
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (mu0 : Measure (X 0)) [IsProbabilityMeasure mu0]
    (K : (n : ℕ) → Kernel ((i : Finset.Iic n) → X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (K n)] :
    (Kernel.trajMeasure mu0 K).map (fun z ↦ z 0) = mu0 := by
  have hevalMeas : Measurable (fun z : (n : ℕ) → X n ↦ z 0) :=
    measurable_pi_apply 0
  rw [Kernel.trajMeasure, Measure.map_comp _ _ hevalMeas]
  have hrestrict := Kernel.traj_map_frestrictLe_of_le
    (κ := K) (show 0 ≤ 0 from le_rfl)
  have heval : (fun z : (n : ℕ) → X n ↦ z 0) =
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        (Preorder.frestrictLe 0) := by
    funext z
    rfl
  rw [heval]
  have hmap : (Kernel.traj K 0).map
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        Preorder.frestrictLe 0) =
      ((Kernel.traj K 0).map (Preorder.frestrictLe 0)).map
        (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) := by
    exact Kernel.map_comp_right _
      (Preorder.measurable_frestrictLe 0)
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable
  change ((Kernel.traj K 0).map
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)) ∘
        Preorder.frestrictLe 0)) ∘ₘ
      (mu0.map (MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 ↦ X i)).symm) = mu0
  rw [hmap, hrestrict]
  rw [Kernel.deterministic_map
    (Preorder.measurable_frestrictLe₂ le_rfl)
    (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)).measurable]
  change (fun q ↦ Measure.dirac
      ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i))
        (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q))) ∘ₘ
      (mu0.map (MeasurableEquiv.piUnique
        (fun i : Finset.Iic 0 ↦ X i)).symm) = mu0
  let e := MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ X i)
  have hf : Measurable (fun q ↦
      e (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q)) :=
    e.measurable.comp (Preorder.measurable_frestrictLe₂ le_rfl)
  change (fun q ↦ Measure.dirac
      (e (Preorder.frestrictLe₂ (show 0 ≤ 0 from le_rfl) q))) ∘ₘ
      (mu0.map e.symm) = mu0
  rw [Measure.bind_dirac_eq_map _ hf]
  change (mu0.map e.symm).map e = mu0
  exact MeasurableEquiv.map_map_symm e


theorem map_markovChainMeasure_prefix_next
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) (u : ℕ) :
    ((markovChainMeasure P x).map
      (Preorder.frestrictLe u)).compProd (markovChainStep P u) =
      (markovChainMeasure P x).map
        (fun omega ↦ (Preorder.frestrictLe u omega, omega (u + 1))) := by
  rw [markovChainMeasure]
  exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

theorem map_markovBanditStackMeasure_initialStates
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S) :
    (markovBanditStackMeasure P x).map (fun omega ↦ fun i ↦ omega i 0) =
      Measure.dirac x := by
  have hi : ∀ i : Fin k,
      (markovChainMeasure P (x i)).map (fun omega ↦ omega 0) =
        Measure.dirac (x i) := by
    intro i
    rw [markovChainMeasure]
    exact map_eval_zero_trajMeasure _ _
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : ∀ i : Fin k, IsProbabilityMeasure
      ((markovChainMeasure P (x i)).map (fun omega ↦ omega 0)) :=
    fun _ ↦ Measure.isProbabilityMeasure_map
      (measurable_pi_apply 0).aemeasurable
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun i ↦ markovChainMeasure P (x i))).map
      (fun omega i ↦ (fun path : ℕ → S ↦ path 0) (omega i)) =
    Measure.dirac x
  rw [Measure.pi_map_pi
    (fun _i ↦ (measurable_pi_apply 0).aemeasurable)]
  simp_rw [hi]
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' x (MeasurableSet.univ_pi hs)]
  conv_rhs =>
    enter [2, i]
    rw [Measure.dirac_apply' (x i) (hs i)]
  classical
  by_cases hx : ∀ i, x i ∈ s i
  · simp [Set.mem_pi, hx]
  · rw [Set.indicator_of_notMem (by simpa [Set.mem_pi] using hx)]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Set.indicator, hi]

abbrev MarkovBanditStackPrefixSpace
    (k : ℕ) (S : Type*) (m : Fin k → ℕ) :=
  ∀ i : Fin k, Finset.Iic (m i) → S

def markovBanditStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ)
    (omega : MarkovBanditStackSpace k S) :
    MarkovBanditStackPrefixSpace k S m :=
  fun i t ↦ omega i t

lemma measurable_markovBanditStackPrefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) :
    Measurable (markovBanditStackPrefixes (S := S) m) := by
  rw [measurable_pi_iff]
  intro i
  rw [measurable_pi_iff]
  intro t
  exact (measurable_pi_apply (t : ℕ)).comp (measurable_pi_apply i)

theorem map_markovBanditStackMeasure_prefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : Fin k → S)
    (m : Fin k → ℕ) :
    (markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m) =
      Measure.pi (fun i ↦
        (markovChainMeasure P (x i)).map (Preorder.frestrictLe (m i))) := by
  letI : ∀ i : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x i)) := fun i ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun i ↦ markovChainMeasure P (x i))).map
      (fun omega i ↦ Preorder.frestrictLe (m i) (omega i)) = _
  exact Measure.pi_map_pi
    (fun i ↦ (Preorder.measurable_frestrictLe (m i)).aemeasurable)


end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

def swapMiddle {A B C : Type*} : (A × B) × C → (A × C) × B :=
  fun q ↦ ((q.1.1, q.2), q.1.2)

lemma measurable_swapMiddle
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] :
    Measurable (swapMiddle (A := A) (B := B) (C := C)) := by
  exact ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

lemma kernel_const_compProd_comap_fst_eq_prod
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (nu : Measure B) [SFinite nu]
    (K : Kernel A C) [IsSFiniteKernel K] :
    (Kernel.const A nu) ⊗ₖ (K.comap Prod.fst measurable_fst) =
      (Kernel.const A nu) ×ₖ K := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp only [Kernel.comap_apply, Kernel.const_apply, Kernel.prod_apply]
  rw [Measure.prod_apply hs]

lemma kernel_prod_eq_compProd_const
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (K : Kernel A B) [IsSFiniteKernel K]
    (nu : Measure C) [SFinite nu] :
    K ×ₖ (Kernel.const A nu) =
      K ⊗ₖ ((Kernel.const (A × B) nu)) := by
  ext a s hs
  rw [Kernel.compProd_apply hs]
  simp only [Kernel.const_apply, Kernel.prod_apply]
  rw [Measure.prod_apply hs]

set_option maxHeartbeats 800000 in
theorem compProd_prod_comap_fst_reorder
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C]
    (mu : Measure A) [SFinite mu]
    (nu : Measure B) [SFinite nu]
    (K : Kernel A C) [IsSFiniteKernel K] :
    (((mu.prod nu).compProd (K.comap Prod.fst measurable_fst)).map
        (swapMiddle (A := A) (B := B) (C := C))) =
      (mu.compProd K).prod nu := by
  let KB : Kernel A B := Kernel.const A nu
  let eta : Kernel (A × B) C := K.comap Prod.fst measurable_fst
  have hk : KB ⊗ₖ eta = KB ×ₖ K := by
    exact kernel_const_compProd_comap_fst_eq_prod nu K
  have hswap : (KB ×ₖ K).map MeasurableEquiv.prodComm =
      K ×ₖ KB := Kernel.prodComm_prod
  have hright : K ×ₖ KB =
      K ⊗ₖ Kernel.const (A × C) nu := by
    exact kernel_prod_eq_compProd_const K nu
  rw [show mu.prod nu = mu ⊗ₘ KB by simp [KB]]
  rw [show (mu.compProd K).prod nu =
      (mu.compProd K) ⊗ₘ Kernel.const (A × C) nu by simp]
  change ((mu ⊗ₘ KB ⊗ₘ eta).map swapMiddle) =
    mu ⊗ₘ K ⊗ₘ Kernel.const (A × C) nu
  rw [← Measure.compProd_assoc]
  rw [hk]
  rw [← Measure.compProd_assoc]
  rw [← hright]
  rw [← hswap]
  rw [MeasureTheory.Measure.compProd_map
    MeasurableEquiv.prodComm.measurable]
  rw [Measure.map_map measurable_swapMiddle
      MeasurableEquiv.prodAssoc.symm.measurable,
    Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      (measurable_id.prodMap MeasurableEquiv.prodComm.measurable)]
  congr 1

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

noncomputable def swapMiddleEquiv
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] :
    ((A × B) × C) ≃ᵐ ((A × C) × B) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl A).prodCongr MeasurableEquiv.prodComm) |>.trans
      MeasurableEquiv.prodAssoc.symm

lemma map_prodMap_equiv_compProd_comap
    {A D C : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace C]
    (e : A ≃ᵐ D) (mu : Measure A) [SFinite mu]
    (K : Kernel D C) [IsSFiniteKernel K] :
    (mu.compProd (K.comap e e.measurable)).map (Prod.map e id) =
      (mu.map e).compProd K := by
  ext s hs
  rw [Measure.map_apply (e.measurable.prodMap measurable_id) hs]
  rw [Measure.compProd_apply (hs.preimage
    (e.measurable.prodMap measurable_id))]
  rw [Measure.compProd_apply hs]
  simp only [Kernel.comap_apply]
  rw [MeasureTheory.lintegral_map'
    (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    e.measurable.aemeasurable]
  apply lintegral_congr
  intro a
  congr 1

lemma map_prodMap_compProd_comap
    {A D C : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [MeasurableSpace C]
    (f : A → D) (hf : Measurable f)
    (mu : Measure A) [SFinite mu]
    (K : Kernel D C) [IsSFiniteKernel K] :
    (mu.compProd (K.comap f hf)).map (Prod.map f id) =
      (mu.map f).compProd K := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs]
  rw [Measure.compProd_apply (hs.preimage
    (hf.prodMap measurable_id))]
  rw [Measure.compProd_apply hs]
  simp only [Kernel.comap_apply]
  rw [MeasureTheory.lintegral_map'
    (Kernel.measurable_kernel_prodMk_left hs).aemeasurable
    hf.aemeasurable]
  apply lintegral_congr
  intro a
  congr 1

lemma withDensity_compProd_left
    {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]
    (mu : Measure A) [SFinite mu]
    (K : Kernel A C) [IsSFiniteKernel K]
    (w : A → ENNReal) (hw : Measurable w) :
    (mu.withDensity w).compProd K =
      (mu.compProd K).withDensity (w ∘ Prod.fst) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [lintegral_withDensity_eq_lintegral_mul mu hw
    (Kernel.measurable_kernel_prodMk_left hs)]
  rw [withDensity_apply (w ∘ Prod.fst) hs]
  rw [← MeasureTheory.lintegral_indicator hs]
  rw [Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    simp only [Pi.mul_apply]
    rw [show (fun c ↦ s.indicator (w ∘ Prod.fst) (a, c)) =
        (Prod.mk a ⁻¹' s).indicator (fun _ ↦ w a) by
          rfl]
    rw [lintegral_indicator (measurable_prodMk_left hs)]
    simp
  · exact (hw.comp measurable_fst).indicator hs

lemma map_withDensity_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (f : A → B) (hf : Measurable f)
    (w : B → ENNReal) (hw : Measurable w) :
    (mu.withDensity (w ∘ f)).map f = (mu.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs]
  rw [withDensity_apply (w ∘ f) (hs.preimage hf)]
  rw [withDensity_apply w hs]
  rw [← lintegral_indicator (hs.preimage hf)]
  rw [← lintegral_indicator hs]
  rw [lintegral_map' (hw.indicator hs).aemeasurable hf.aemeasurable]
  apply lintegral_congr
  intro a
  rfl

lemma withDensity_withDensity_of_measurable
    {A : Type*} [MeasurableSpace A]
    (mu : Measure A) (w v : A → ENNReal)
    (hw : Measurable w) (hv : Measurable v) :
    (mu.withDensity w).withDensity v = mu.withDensity (w * v) := by
  ext s hs
  rw [withDensity_apply v hs]
  rw [setLIntegral_withDensity_eq_setLIntegral_mul
    mu hw hv hs]
  rw [withDensity_apply (w * v) hs]

lemma map_withDensity_mul_comp
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (f : A → B) (hf : Measurable f)
    (w : A → ENNReal) (hw : Measurable w)
    (v : B → ENNReal) (hv : Measurable v) :
    (mu.withDensity (w * (v ∘ f))).map f =
      ((mu.withDensity w).map f).withDensity v := by
  rw [← withDensity_withDensity_of_measurable mu w (v ∘ f)
    hw (hv.comp hf)]
  exact map_withDensity_comp (mu.withDensity w) f hf v hv

abbrev OtherArm {k : ℕ} (i : Fin k) := {j : Fin k // j ≠ i}
abbrev SelectedArm {k : ℕ} (i : Fin k) := {j : Fin k // j = i}

noncomputable def splitStackAt
    {k : ℕ} {S : Type*} [MeasurableSpace S] (i : Fin k) :
    MarkovBanditStackSpace k S ≃ᵐ
      ((ℕ → S) × (OtherArm i → ℕ → S)) := by
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  exact (MeasurableEquiv.piEquivPiSubtypeProd
      (fun _ : Fin k ↦ ℕ → S) (fun j ↦ j = i)).trans
    ((MeasurableEquiv.piUnique
      (fun _ : SelectedArm i ↦ ℕ → S)).prodCongr
        (MeasurableEquiv.refl (OtherArm i → ℕ → S)))

abbrev OtherPrefixSpace
    {k : ℕ} (S : Type*) (m : Fin k → ℕ) (i : Fin k) :=
  ∀ j : OtherArm i, Finset.Iic (m j) → S

noncomputable def splitStackPrefixAt
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    MarkovBanditStackPrefixSpace k S m ≃ᵐ
      ((Finset.Iic (m i) → S) × OtherPrefixSpace S m i) := by
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  exact (MeasurableEquiv.piEquivPiSubtypeProd
      (fun j : Fin k ↦ Finset.Iic (m j) → S)
      (fun j ↦ j = i)).trans
    ((MeasurableEquiv.piUnique
      (fun j : SelectedArm i ↦ Finset.Iic (m j) → S)).prodCongr
        (MeasurableEquiv.refl (OtherPrefixSpace S m i)))

theorem map_splitStackAt_markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (i : Fin k) :
    (markovBanditStackMeasure P x).map (splitStackAt (S := S) i) =
      (markovChainMeasure P (x i)).prod
        (Measure.pi (fun j : OtherArm i ↦
          markovChainMeasure P (x j))) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : Fintype (SelectedArm i) := Subtype.fintype (fun j ↦ j = i)
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Fin k ↦ ℕ → S) (fun j ↦ j = i)
  let e1 := MeasurableEquiv.piUnique
    (fun _ : SelectedArm i ↦ ℕ → S)
  have hsplit :
      (Measure.pi (fun j : Fin k ↦ markovChainMeasure P (x j))).map e0 =
        (Measure.pi (fun j : SelectedArm i ↦
          markovChainMeasure P (x j))).prod
          (Measure.pi (fun j : OtherArm i ↦
            markovChainMeasure P (x j))) :=
    (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      (fun j : Fin k ↦ markovChainMeasure P (x j))
      (fun j ↦ j = i)).map_eq
  have hsel :
      (Measure.pi (fun j : SelectedArm i ↦
        markovChainMeasure P (x j))).map e1 =
          markovChainMeasure P (x i) := by
    change (Measure.pi (fun j : SelectedArm i ↦
      markovChainMeasure P (x j))).map (Function.eval default) = _
    rw [Measure.pi_map_eval]
    simp [show ((default : SelectedArm i) : Fin k) = i from
      Subtype.property (default : SelectedArm i)]
  rw [markovBanditStackMeasure]
  change (Measure.pi (fun j : Fin k ↦
      markovChainMeasure P (x j))).map
        ((e1.prodCongr (MeasurableEquiv.refl
          (OtherArm i → ℕ → S))) ∘ e0) = _
  rw [← Measure.map_map
    (e1.prodCongr (MeasurableEquiv.refl
      (OtherArm i → ℕ → S))).measurable e0.measurable]
  rw [hsplit]
  change ((Measure.pi (fun j : SelectedArm i ↦
      markovChainMeasure P (x j))).prod
        (Measure.pi (fun j : OtherArm i ↦
          markovChainMeasure P (x j)))).map
      (Prod.map e1 id) = _
  rw [← Measure.map_prod_map _ _ e1.measurable measurable_id]
  rw [hsel, Measure.map_id]

theorem map_splitStackPrefixAt_markovBanditStackMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    (markovBanditStackMeasure P x).map
        ((splitStackPrefixAt (S := S) m i) ∘
          markovBanditStackPrefixes m) =
      ((markovChainMeasure P (x i)).map
          (Preorder.frestrictLe (m i))).prod
        (Measure.pi (fun j : OtherArm i ↦
          (markovChainMeasure P (x j)).map
            (Preorder.frestrictLe (m j)))) := by
  let ν : ∀ j : Fin k, Measure (Finset.Iic (m j) → S) :=
    fun j ↦ (markovChainMeasure P (x j)).map
      (Preorder.frestrictLe (m j))
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : ∀ j : Fin k, IsProbabilityMeasure (ν j) := fun j ↦ by
    dsimp [ν]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m j)).aemeasurable
  letI : Fintype (SelectedArm i) := Subtype.fintype (fun j ↦ j = i)
  letI : Unique (SelectedArm i) :=
    { default := ⟨i, rfl⟩
      uniq := fun j ↦ Subtype.ext j.property }
  let e0 := MeasurableEquiv.piEquivPiSubtypeProd
    (fun j : Fin k ↦ Finset.Iic (m j) → S) (fun j ↦ j = i)
  let e1 := MeasurableEquiv.piUnique
    (fun j : SelectedArm i ↦ Finset.Iic (m j) → S)
  have hsplit :
      (Measure.pi ν).map e0 =
        (Measure.pi (fun j : SelectedArm i ↦ ν j)).prod
          (Measure.pi (fun j : OtherArm i ↦ ν j)) :=
    (MeasureTheory.measurePreserving_piEquivPiSubtypeProd
      ν (fun j ↦ j = i)).map_eq
  have hsel :
      (Measure.pi (fun j : SelectedArm i ↦ ν j)).map e1 =
          ν i := by
    change (Measure.pi (fun j : SelectedArm i ↦ ν j)).map
      (Function.eval default) = _
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul]
    change ν (⟨i, rfl⟩ : SelectedArm i) = ν i
    rfl
  rw [← Measure.map_map
    (splitStackPrefixAt (S := S) m i).measurable
    (measurable_markovBanditStackPrefixes m)]
  rw [map_markovBanditStackMeasure_prefixes]
  change (Measure.pi ν).map
      ((e1.prodCongr (MeasurableEquiv.refl
        (OtherPrefixSpace S m i))) ∘ e0) = _
  rw [← Measure.map_map
    (e1.prodCongr (MeasurableEquiv.refl
      (OtherPrefixSpace S m i))).measurable e0.measurable]
  rw [hsplit]
  change ((Measure.pi (fun j : SelectedArm i ↦ ν j)).prod
      (Measure.pi (fun j : OtherArm i ↦ ν j))).map
        (Prod.map e1 id) = _
  rw [← Measure.map_prod_map _ _ e1.measurable measurable_id]
  rw [hsel, Measure.map_id]

def otherStackPrefixes
    {k : ℕ} {S : Type*} (m : Fin k → ℕ) (i : Fin k)
    (omega : OtherArm i → ℕ → S) : OtherPrefixSpace S m i :=
  fun j t ↦ omega j t

lemma measurable_otherStackPrefixes
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    Measurable (otherStackPrefixes (S := S) m i) := by
  rw [measurable_pi_iff]
  intro j
  rw [measurable_pi_iff]
  intro t
  exact (measurable_pi_apply (t : ℕ)).comp (measurable_pi_apply j)

theorem map_markovBanditStackMeasure_selected_prefix_next_other
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    (markovBanditStackMeasure P x).map (fun omega ↦
        ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
          fun j : OtherArm i ↦
            Preorder.frestrictLe (m j) (omega j))) =
      ((markovChainMeasure P (x i)).map (fun path ↦
          (Preorder.frestrictLe (m i) path, path (m i + 1)))).prod
        (Measure.pi (fun j : OtherArm i ↦
          (markovChainMeasure P (x j)).map
            (Preorder.frestrictLe (m j)))) := by
  letI : ∀ j : Fin k,
      IsProbabilityMeasure (markovChainMeasure P (x j)) := fun j ↦ by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : IsProbabilityMeasure
      (Measure.pi (fun j : OtherArm i ↦
        markovChainMeasure P (x j))) := by infer_instance
  let f : (ℕ → S) → ((Finset.Iic (m i) → S) × S) :=
    fun path ↦ (Preorder.frestrictLe (m i) path, path (m i + 1))
  let g : (OtherArm i → ℕ → S) → OtherPrefixSpace S m i :=
    otherStackPrefixes m i
  have hf : Measurable f :=
    (Preorder.measurable_frestrictLe (m i)).prodMk
      (measurable_pi_apply (m i + 1))
  have hg : Measurable g := measurable_otherStackPrefixes m i
  rw [show (fun omega : MarkovBanditStackSpace k S ↦
      ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
        fun j : OtherArm i ↦
          Preorder.frestrictLe (m j) (omega j))) =
      Prod.map f g ∘ splitStackAt (S := S) i by rfl]
  rw [← Measure.map_map (hf.prodMap hg) (splitStackAt (S := S) i).measurable]
  rw [map_splitStackAt_markovBanditStackMeasure]
  rw [← Measure.map_prod_map _ _ hf hg]
  congr 1
  change (Measure.pi (fun j : OtherArm i ↦
      markovChainMeasure P (x j))).map
        (fun omega (j : OtherArm i) ↦
          Preorder.frestrictLe (m j) (omega j)) = _
  exact Measure.pi_map_pi
    (fun j ↦ (Preorder.measurable_frestrictLe (m j)).aemeasurable)

def markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} (m : Fin k → ℕ) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S m) : S :=
  q i ⟨m i, Finset.mem_Iic.2 le_rfl⟩

lemma measurable_markovBanditStackPrefixCurrent
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    Measurable (markovBanditStackPrefixCurrent (S := S) m i) :=
  (measurable_pi_apply _).comp (measurable_pi_apply i)

noncomputable def markovBanditStackPrefixStep
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) (m : Fin k → ℕ) (i : Fin k) :
    Kernel (MarkovBanditStackPrefixSpace k S m) S :=
  P.comap (markovBanditStackPrefixCurrent m i)
    (measurable_markovBanditStackPrefixCurrent m i)

instance markovBanditStackPrefixStep.instIsMarkovKernel
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (m : Fin k → ℕ) (i : Fin k) :
    IsMarkovKernel (markovBanditStackPrefixStep P m i) := by
  rw [markovBanditStackPrefixStep]
  infer_instance

noncomputable def splitStackPrefixNextAt
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (m : Fin k → ℕ) (i : Fin k) :
    (MarkovBanditStackPrefixSpace k S m × S) ≃ᵐ
      (((Finset.Iic (m i) → S) × S) × OtherPrefixSpace S m i) :=
  ((splitStackPrefixAt (S := S) m i).prodCongr
    (MeasurableEquiv.refl S)).trans swapMiddleEquiv

theorem markovBanditStackMeasure_prefix_transition
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k) :
    ((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m)).compProd
          (markovBanditStackPrefixStep P m i) =
      (markovBanditStackMeasure P x).map (fun omega ↦
        (markovBanditStackPrefixes m omega, omega i (m i + 1))) := by
  let E := splitStackPrefixAt (S := S) m i
  let K : Kernel
      ((Finset.Iic (m i) → S) × OtherPrefixSpace S m i) S :=
    (markovChainStep P (m i)).comap Prod.fst measurable_fst
  let μ := (markovChainMeasure P (x i)).map
    (Preorder.frestrictLe (m i))
  let ν := Measure.pi (fun j : OtherArm i ↦
    (markovChainMeasure P (x j)).map
      (Preorder.frestrictLe (m j)))
  let M := (markovBanditStackMeasure P x).map
    (markovBanditStackPrefixes (S := S) m)
  let F := splitStackPrefixNextAt (S := S) m i
  letI : IsProbabilityMeasure (markovChainMeasure P (x i)) := by
    rw [← markovChainKernel_apply]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m i)).aemeasurable
  letI : ∀ j : OtherArm i,
      IsProbabilityMeasure ((markovChainMeasure P (x j)).map
        (Preorder.frestrictLe (m j))) := fun j ↦ by
    letI : IsProbabilityMeasure (markovChainMeasure P (x j)) := by
      rw [← markovChainKernel_apply]
      infer_instance
    exact Measure.isProbabilityMeasure_map
      (Preorder.measurable_frestrictLe (m j)).aemeasurable
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  have hstep : markovBanditStackPrefixStep P m i =
      K.comap E E.measurable := by
    rfl
  have hbase : M.map E = μ.prod ν := by
    dsimp [M, μ, ν]
    rw [Measure.map_map E.measurable
      (measurable_markovBanditStackPrefixes m)]
    exact map_splitStackPrefixAt_markovBanditStackMeasure P x m i
  have hleft :
      (M.compProd (markovBanditStackPrefixStep P m i)).map F =
        (μ.compProd (markovChainStep P (m i))).prod ν := by
    rw [hstep]
    change (M.compProd (K.comap E E.measurable)).map
        (swapMiddleEquiv ∘ Prod.map E id) = _
    rw [← Measure.map_map swapMiddleEquiv.measurable
      (E.measurable.prodMap measurable_id)]
    rw [map_prodMap_equiv_compProd_comap E M K]
    rw [hbase]
    exact compProd_prod_comap_fst_reorder μ ν
      (markovChainStep P (m i))
  have hright :
      ((markovBanditStackMeasure P x).map (fun omega ↦
          (markovBanditStackPrefixes m omega, omega i (m i + 1)))).map F =
        (μ.compProd (markovChainStep P (m i))).prod ν := by
    rw [Measure.map_map F.measurable
      ((measurable_markovBanditStackPrefixes m).prodMk
        ((measurable_pi_apply (m i + 1)).comp
          (measurable_pi_apply i)))]
    change (markovBanditStackMeasure P x).map (fun omega ↦
        ((Preorder.frestrictLe (m i) (omega i), omega i (m i + 1)),
          fun j : OtherArm i ↦
            Preorder.frestrictLe (m j) (omega j))) = _
    rw [map_markovBanditStackMeasure_selected_prefix_next_other]
    rw [map_markovChainMeasure_prefix_next]
  apply F.map_measurableEquiv_injective
  rw [hleft, hright]

theorem markovBanditStackMeasure_weighted_prefix_transition
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (x : Fin k → S) (m : Fin k → ℕ) (i : Fin k)
    (w : MarkovBanditStackPrefixSpace k S m → ENNReal)
    (hw : Measurable w) :
    (((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes (S := S) m)).withDensity w).compProd
          (markovBanditStackPrefixStep P m i) =
      ((markovBanditStackMeasure P x).map (fun omega ↦
        (markovBanditStackPrefixes m omega, omega i (m i + 1)))).withDensity
          (w ∘ Prod.fst) := by
  rw [withDensity_compProd_left]
  rw [markovBanditStackMeasure_prefix_transition]
  exact hw

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

lemma finiteStackPullCountBefore_mono
    {k n : ℕ} (a : Fin n → Fin k) (i : Fin k)
    {s t : ℕ} (hst : s ≤ t) :
    finiteStackPullCountBefore a i s ≤
      finiteStackPullCountBefore a i t := by
  classical
  apply Finset.sum_le_sum
  intro u hu
  by_cases hs : (u : ℕ) < s ∧ a u = i
  · have ht : (u : ℕ) < t ∧ a u = i :=
      ⟨lt_of_lt_of_le hs.1 hst, hs.2⟩
    simp [hs, ht]
  · simp [hs]

def markovBanditPrefixHistory
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) :
    MarkovBanditHistory k S n :=
  (fun t ↦
      (fun i ↦ q i ⟨finiteStackPullCountBefore a i t,
        Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
          (Nat.le_of_lt t.isLt))⟩,
        a t),
    fun i ↦ q i ⟨finiteStackPullCountBefore a i n,
      Finset.mem_Iic.2 le_rfl⟩)

lemma measurable_markovBanditPrefixHistory
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (a : Fin n → Fin k) :
    Measurable (markovBanditPrefixHistory (S := S) a) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro t
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply _).comp (measurable_pi_apply i)
    · exact measurable_const
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply i)

lemma markovBanditPrefixHistory_stackPrefixes
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S) (a : Fin n → Fin k) :
    markovBanditPrefixHistory a
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) omega) =
      markovBanditFiniteStackHistory omega a := by
  rfl

lemma finiteStackPullCountBefore_snoc_old
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k) :
    finiteStackPullCountBefore (Fin.snoc a i) j n =
      finiteStackPullCountBefore a j n := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht, Fin.castLE]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j n =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j n := by
          rw [has]
    _ = stackPullCountBefore b j n :=
      finiteStackPullCountBefore_restrict b j n (Nat.le_succ n)
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j n :=
      (finiteStackPullCountBefore_restrict b j n le_rfl).symm
    _ = finiteStackPullCountBefore a j n := by rw [ha]

lemma finiteStackPullCountBefore_snoc_before
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k)
    (s : ℕ) (hs : s ≤ n) :
    finiteStackPullCountBefore (Fin.snoc a i) j s =
      finiteStackPullCountBefore a j s := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j s =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j s := by
          rw [has]
    _ = stackPullCountBefore b j s :=
      finiteStackPullCountBefore_restrict b j s (hs.trans (Nat.le_succ n))
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j s :=
      (finiteStackPullCountBefore_restrict b j s hs).symm
    _ = finiteStackPullCountBefore a j s := by rw [ha]

lemma finiteStackPullCountBefore_snoc_succ
    {k n : ℕ} (a : Fin n → Fin k) (j i : Fin k) :
    finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) =
      finiteStackPullCountBefore a j n + if i = j then 1 else 0 := by
  let b : ℕ → Fin k := fun t ↦
    if h : t < n then a ⟨t, h⟩ else i
  have ha : (fun t : Fin n ↦ b t) = a := by
    funext t
    simp [b, t.isLt]
  have has : (fun t : Fin (n + 1) ↦ b t) = Fin.snoc a i := by
    funext t
    by_cases ht : (t : ℕ) < n
    · simp only [b, dif_pos ht, Fin.snoc, ht, Fin.castLE]
      congr 1
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      simp [b, Fin.snoc]
  calc
    finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) =
        finiteStackPullCountBefore (fun t : Fin (n + 1) ↦ b t) j (n + 1) := by
          rw [has]
    _ = stackPullCountBefore b j (n + 1) :=
      finiteStackPullCountBefore_restrict b j (n + 1) le_rfl
    _ = stackPullCountBefore b j n + if b n = j then 1 else 0 := by
      rw [stackPullCountBefore_succ]
    _ = finiteStackPullCountBefore (fun t : Fin n ↦ b t) j n +
        if i = j then 1 else 0 := by
      rw [finiteStackPullCountBefore_restrict b j n le_rfl]
      simp [b]
    _ = finiteStackPullCountBefore a j n + if i = j then 1 else 0 := by
      rw [ha]

def markovBanditPrefixHistoryBefore
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n))
    (t : Fin (n + 1)) : MarkovBanditHistory k S t :=
  (fun u ↦
      (fun i ↦ q i ⟨finiteStackPullCountBefore a i u,
        Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
          (Nat.le_trans (Nat.le_of_lt u.isLt) (Nat.le_of_lt_succ t.isLt)))⟩,
        a ⟨u, lt_of_lt_of_le u.isLt (Nat.le_of_lt_succ t.isLt)⟩),
    fun i ↦ q i ⟨finiteStackPullCountBefore a i t,
      Finset.mem_Iic.2 (finiteStackPullCountBefore_mono a i
        (Nat.le_of_lt_succ t.isLt))⟩)

lemma measurable_markovBanditPrefixHistoryBefore
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (a : Fin n → Fin k) (t : Fin (n + 1)) :
    Measurable (markovBanditPrefixHistoryBefore (S := S) a · t) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro u
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro i
      exact (measurable_pi_apply _).comp (measurable_pi_apply i)
    · exact measurable_const
  · rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply _).comp (measurable_pi_apply i)

noncomputable def markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun i ↦ finiteStackPullCountBefore a i n)) : ENNReal :=
  ∏ t : Fin n,
    (pi.select t) (markovBanditPrefixHistoryBefore a q t.castSucc) {a t}

lemma measurable_markovBanditActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) :
    Measurable (markovBanditActionLikelihood pi a) := by
  apply Finset.measurable_prod
  intro t ht
  exact ((pi.select t).measurable_coe (MeasurableSet.singleton (a t))).comp
    (measurable_markovBanditPrefixHistoryBefore a t.castSucc)

def markovBanditSnocOldPrefix
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore a j n) :=
  fun j u ↦ q j ⟨u, Finset.mem_Iic.2 <|
    le_trans (Finset.mem_Iic.1 u.property) <| by
      calc
        finiteStackPullCountBefore a j n ≤
            finiteStackPullCountBefore a j n + if i = j then 1 else 0 :=
          Nat.le_add_right _ _
        _ = finiteStackPullCountBefore (Fin.snoc a i) j (n + 1) :=
          (finiteStackPullCountBefore_snoc_succ a j i).symm⟩

lemma markovBanditPrefixHistoryBefore_snoc_castSucc
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1)))
    (t : Fin n) :
    markovBanditPrefixHistoryBefore (Fin.snoc a i) q t.castSucc.castSucc =
      markovBanditPrefixHistoryBefore a
        (markovBanditSnocOldPrefix a i q) t.castSucc := by
  apply Prod.ext
  · funext u
    apply Prod.ext
    · funext j
      simp only [markovBanditPrefixHistoryBefore,
        markovBanditSnocOldPrefix]
      congr 2
      exact finiteStackPullCountBefore_snoc_before a j i u
        (by omega)
    · simp only [markovBanditPrefixHistoryBefore]
      have hu : (u : ℕ) < n := lt_trans u.isLt t.isLt
      simp [Fin.snoc, hu]
  · funext j
    simp only [markovBanditPrefixHistoryBefore,
      markovBanditSnocOldPrefix]
    congr 2
    exact finiteStackPullCountBefore_snoc_before a j i t
      (Nat.le_of_lt t.isLt)

lemma markovBanditPrefixHistoryBefore_snoc_last
    {k n : ℕ} {S : Type*}
    (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    markovBanditPrefixHistoryBefore (Fin.snoc a i) q (Fin.last n).castSucc =
      markovBanditPrefixHistory a (markovBanditSnocOldPrefix a i q) := by
  apply Prod.ext
  · funext u
    apply Prod.ext
    · funext j
      simp only [markovBanditPrefixHistoryBefore,
        markovBanditPrefixHistory, markovBanditSnocOldPrefix]
      congr 2
      exact finiteStackPullCountBefore_snoc_before a j i u
        (Nat.le_of_lt u.isLt)
    · simp only [markovBanditPrefixHistoryBefore,
        markovBanditPrefixHistory]
      have hu : (u : ℕ) < n := u.isLt
      simp [Fin.snoc, hu]
  · funext j
    simp only [markovBanditPrefixHistoryBefore,
      markovBanditPrefixHistory, markovBanditSnocOldPrefix]
    congr 2
    exact finiteStackPullCountBefore_snoc_old a j i

lemma markovBanditActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) (i : Fin k)
    (q : MarkovBanditStackPrefixSpace k S
      (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))) :
    markovBanditActionLikelihood pi (Fin.snoc a i) q =
      markovBanditActionLikelihood pi a (markovBanditSnocOldPrefix a i q) *
        (pi.select n)
          (markovBanditPrefixHistory a (markovBanditSnocOldPrefix a i q)) {i} := by
  rw [markovBanditActionLikelihood, Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t ht
    rw [Fin.snoc_castSucc]
    rw [markovBanditPrefixHistoryBefore_snoc_castSucc]
    rfl
  · rw [Fin.snoc_last]
    rw [markovBanditPrefixHistoryBefore_snoc_last]
    rfl

noncomputable def markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k)
    (omega : MarkovBanditStackSpace k S) : ENNReal :=
  markovBanditActionLikelihood pi a
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n) omega)

lemma measurable_markovBanditStackActionLikelihood
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (a : Fin n → Fin k) :
    Measurable (markovBanditStackActionLikelihood pi a) :=
  (measurable_markovBanditActionLikelihood pi a).comp
    (measurable_markovBanditStackPrefixes _)

lemma markovBanditSnocOldPrefix_stackPrefixes
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditSnocOldPrefix a i
        (markovBanditStackPrefixes
          (fun j ↦ finiteStackPullCountBefore (Fin.snoc a i) j (n + 1))
          omega) =
      markovBanditStackPrefixes
        (fun j ↦ finiteStackPullCountBefore a j n) omega := by
  rfl

lemma markovBanditStackActionLikelihood_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditStackActionLikelihood pi (Fin.snoc a i) omega =
      markovBanditStackActionLikelihood pi a omega *
        (pi.select n) (markovBanditFiniteStackHistory omega a) {i} := by
  rw [markovBanditStackActionLikelihood,
    markovBanditActionLikelihood_snoc]
  rw [markovBanditSnocOldPrefix_stackPrefixes]
  rw [markovBanditPrefixHistory_stackPrefixes]
  rfl

noncomputable def markovBanditFixedActionHistoryMeasure
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) : Measure (MarkovBanditHistory k S n) :=
  ((markovBanditStackMeasure P x).withDensity
      (markovBanditStackActionLikelihood pi a)).map
    (fun omega ↦ markovBanditFiniteStackHistory omega a)

instance markovBanditFixedActionHistoryMeasure.instSFinite
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    SFinite (markovBanditFixedActionHistoryMeasure P pi x a) := by
  rw [markovBanditFixedActionHistoryMeasure]
  infer_instance

lemma markovBanditFixedActionHistoryMeasure_eq_prefix
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) :
    markovBanditFixedActionHistoryMeasure P pi x a =
      (((markovBanditStackMeasure P x).map
        (markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n))).withDensity
            (markovBanditActionLikelihood pi a)).map
        (markovBanditPrefixHistory a) := by
  rw [markovBanditFixedActionHistoryMeasure]
  rw [show (fun omega ↦ markovBanditFiniteStackHistory omega a) =
      markovBanditPrefixHistory a ∘
        markovBanditStackPrefixes
          (fun i ↦ finiteStackPullCountBefore a i n) by
        funext omega
        exact (markovBanditPrefixHistory_stackPrefixes omega a).symm]
  rw [← Measure.map_map (measurable_markovBanditPrefixHistory a)
    (measurable_markovBanditStackPrefixes _)]
  congr 1
  exact map_withDensity_comp
    (markovBanditStackMeasure P x)
    (markovBanditStackPrefixes
      (fun i ↦ finiteStackPullCountBefore a i n))
    (measurable_markovBanditStackPrefixes _)
    (markovBanditActionLikelihood pi a)
    (measurable_markovBanditActionLikelihood pi a)

lemma markovBanditFixedActionHistoryMeasure_zero
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditFixedActionHistoryMeasure P pi x
        (fun t : Fin 0 ↦ t.elim0) =
      markovBanditMeasure P pi x 0 := by
  rw [markovBanditFixedActionHistoryMeasure]
  have hone : markovBanditStackActionLikelihood pi
      (fun t : Fin 0 ↦ t.elim0) = fun _ ↦ 1 := by
    funext omega
    simp [markovBanditStackActionLikelihood,
      markovBanditActionLikelihood]
  rw [hone]
  change ((markovBanditStackMeasure P x).withDensity
      (1 : MarkovBanditStackSpace k S → ENNReal)).map
        (fun omega ↦ markovBanditFiniteStackHistory omega
          (fun t : Fin 0 ↦ t.elim0)) = _
  rw [withDensity_one]
  let f : MarkovBanditStackSpace k S → MarkovBanditHistory k S 0 :=
    fun omega ↦ markovBanditFiniteStackHistory omega
      (fun t : Fin 0 ↦ t.elim0)
  let eval0 : MarkovBanditStackSpace k S → Fin k → S :=
    fun omega i ↦ omega i 0
  let mk0 : (Fin k → S) → MarkovBanditHistory k S 0 :=
    fun y ↦ (fun t : Fin 0 ↦ t.elim0, y)
  have heval0 : Measurable eval0 := by
    rw [measurable_pi_iff]
    intro i
    exact (measurable_pi_apply 0).comp (measurable_pi_apply i)
  have hmk0 : Measurable mk0 :=
    (measurable_pi_lambda _ fun t ↦ t.elim0).prodMk measurable_id
  change (markovBanditStackMeasure P x).map f = _
  rw [show f = mk0 ∘ eval0 by
    funext omega
    apply Prod.ext
    · funext t
      exact Fin.elim0 t
    · rfl]
  rw [← Measure.map_map hmk0 heval0]
  rw [map_markovBanditStackMeasure_initialStates]
  rw [Measure.map_dirac]
  rfl

def markovBanditHistorySnocFixed
    {k n : ℕ} {S : Type*} (i : Fin k)
    (p : MarkovBanditHistory k S n × S) :
    MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc p.1.1 (p.1.2, i), Function.update p.1.2 i p.2)

lemma measurable_markovBanditHistorySnocFixed
    {k n : ℕ} {S : Type*} [MeasurableSpace S] (i : Fin k) :
    Measurable (markovBanditHistorySnocFixed (n := n) (S := S) i) := by
  exact measurable_markovBanditSnoc.comp
    (measurable_fst.prodMk
      (measurable_const.prodMk measurable_snd))

lemma markovBanditFiniteStackHistory_snoc
    {k n : ℕ} {S : Type*}
    (omega : MarkovBanditStackSpace k S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditFiniteStackHistory omega (Fin.snoc a i) =
      markovBanditHistorySnocFixed i
        (markovBanditFiniteStackHistory omega a,
          omega i (finiteStackPullCountBefore a i n + 1)) := by
  apply Prod.ext
  · funext t
    by_cases ht : (t : ℕ) < n
    · apply Prod.ext
      · funext j
        simp only [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc, ht, dite_true]
        change omega j (finiteStackPullCountBefore (Fin.snoc a i) j t) =
          omega j (finiteStackPullCountBefore a j t)
        rw [finiteStackPullCountBefore_snoc_before a j i t
          (Nat.le_of_lt ht)]
      · simp [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc, ht]
    · have htn : (t : ℕ) = n := by omega
      have htlast : t = Fin.last n := Fin.ext htn
      rw [htlast]
      apply Prod.ext
      · funext j
        simp only [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed, Fin.snoc_last]
        change omega j (finiteStackPullCountBefore (Fin.snoc a i) j n) =
          omega j (finiteStackPullCountBefore a j n)
        rw [finiteStackPullCountBefore_snoc_old]
      · simp [markovBanditFiniteStackHistory,
          markovBanditHistorySnocFixed]
  · funext j
    simp only [markovBanditFiniteStackHistory,
      markovBanditHistorySnocFixed]
    rw [finiteStackPullCountBefore_snoc_succ]
    by_cases hji : j = i
    · subst j
      simp
    · simp [Function.update, hji, Ne.symm hji]

noncomputable def markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k)
    (h : MarkovBanditHistory k S n) : ENNReal :=
  (pi.select n) h {i}

lemma measurable_markovBanditSelectMass
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    Measurable (markovBanditSelectMass (n := n) pi i) :=
  (pi.select n).measurable_coe (MeasurableSet.singleton i)

theorem markovBanditFixedActionHistoryMeasure_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S)
    (a : Fin n → Fin k) (i : Fin k) :
    markovBanditFixedActionHistoryMeasure P pi x (Fin.snoc a i) =
      (((markovBanditFixedActionHistoryMeasure P pi x a).withDensity
          (markovBanditSelectMass pi i)).compProd
        (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
          ((measurable_pi_apply i).comp measurable_snd))).map
        (markovBanditHistorySnocFixed i) := by
  let m : Fin k → ℕ := fun j ↦ finiteStackPullCountBefore a j n
  let pref := markovBanditStackPrefixes (S := S) m
  let hist := markovBanditPrefixHistory (S := S) a
  let M := (markovBanditStackMeasure P x).map pref
  let w := markovBanditActionLikelihood pi a
  let v := markovBanditSelectMass (n := n) pi i
  let W : MarkovBanditStackPrefixSpace k S m → ENNReal :=
    w * (v ∘ hist)
  have hpref : Measurable pref := measurable_markovBanditStackPrefixes m
  have hhist : Measurable hist := measurable_markovBanditPrefixHistory a
  have hw : Measurable w := measurable_markovBanditActionLikelihood pi a
  have hv : Measurable v := measurable_markovBanditSelectMass pi i
  have hW : Measurable W := hw.mul (hv.comp hhist)
  have hfixed : markovBanditFixedActionHistoryMeasure P pi x a =
      (M.withDensity w).map hist := by
    simpa [M, m, pref, hist, w] using
      markovBanditFixedActionHistoryMeasure_eq_prefix P pi x a
  have hkernel :
      (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)).comap hist hhist =
        markovBanditStackPrefixStep P m i := by
    rfl
  have hweighted := markovBanditStackMeasure_weighted_prefix_transition
    P x m i W hW
  rw [hfixed]
  rw [← map_withDensity_mul_comp M hist hhist w hw v hv]
  rw [← map_prodMap_compProd_comap hist hhist
    (M.withDensity W)
    (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd))]
  rw [Measure.map_map
    (measurable_markovBanditHistorySnocFixed i)
    (hhist.prodMap measurable_id)]
  rw [hkernel]
  rw [hweighted]
  rw [← map_withDensity_comp]
  rw [Measure.map_map
    ((measurable_markovBanditHistorySnocFixed i).comp
      (hhist.prodMap measurable_id))
    (hpref.prodMk
      ((measurable_pi_apply (m i + 1)).comp (measurable_pi_apply i)))]
  · rw [markovBanditFixedActionHistoryMeasure]
    congr 1
    · funext omega
      exact markovBanditFiniteStackHistory_snoc omega a i
    · congr 1
      funext omega
      rw [markovBanditStackActionLikelihood_snoc]
      rfl
  · exact (hpref.prodMk
      ((measurable_pi_apply (m i + 1)).comp (measurable_pi_apply i)))
  · exact hW.comp measurable_fst

noncomputable def markovBanditFixedActionStepKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    Kernel (MarkovBanditHistory k S n) (Fin k × S) :=
  ((P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)).withDensity
    (fun h _ ↦ markovBanditSelectMass pi i h)).map
      (fun y ↦ (i, y))

instance markovBanditFixedActionStepKernel.instIsSFiniteKernel
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (i : Fin k) :
    IsSFiniteKernel (markovBanditFixedActionStepKernel
      (n := n) P pi i) := by
  let K : Kernel (MarkovBanditHistory k S n) S :=
    P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)
  letI : IsSFiniteKernel (K.withDensity
      (fun h _ ↦ markovBanditSelectMass pi i h)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity K (fun h _ ↦ by
      exact measure_ne_top ((pi.select n) h) {i})
  rw [markovBanditFixedActionStepKernel]
  infer_instance

theorem markovBanditStepKernel_eq_sum_fixedAction
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) :
    markovBanditStepKernel P pi n =
      ∑ i : Fin k, markovBanditFixedActionStepKernel P pi i := by
  ext h s hs
  rw [markovBanditStepKernel, Kernel.compProd_apply hs]
  rw [Kernel.finsetSum_apply' Finset.univ
    (fun i : Fin k ↦ markovBanditFixedActionStepKernel P pi i) h s]
  rw [← Measure.sum_smul_dirac (pi.select n h)]
  rw [lintegral_sum_measure]
  rw [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_smul_measure]
  rw [lintegral_dirac']
  · rw [markovBanditFixedActionStepKernel]
    simp only [smul_eq_mul]
    rw [Kernel.map_apply
      ((P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)).withDensity
          (fun h _ ↦ markovBanditSelectMass pi i h))
      (f := fun y : S ↦ (i, y))
      (measurable_const.prodMk measurable_id) h]
    have hf : Measurable (fun y : S ↦ (i, y)) :=
      measurable_const.prodMk measurable_id
    rw [Measure.map_apply hf hs]
    have hd : Measurable (Function.uncurry
        (fun h : MarkovBanditHistory k S n ↦
          fun _ : S ↦ markovBanditSelectMass pi i h)) :=
      (measurable_markovBanditSelectMass pi i).comp measurable_fst
    rw [Kernel.withDensity_apply'
      (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
        ((measurable_pi_apply i).comp measurable_snd)) hd]
    rw [setLIntegral_const]
    simp [markovBanditSelectMass, Kernel.comap_apply,
      mul_comm]
  · exact Kernel.measurable_kernel_prodMk_left' hs h

def markovBanditHistorySnocGeneral
    {k n : ℕ} {S : Type*}
    (p : MarkovBanditHistory k S n × (Fin k × S)) :
    MarkovBanditHistory k S (n + 1) :=
  (Fin.snoc p.1.1 (p.1.2, p.2.1),
    Function.update p.1.2 p.2.1 p.2.2)

lemma measurable_markovBanditHistorySnocGeneral
    {k n : ℕ} {S : Type*} [MeasurableSpace S] :
    Measurable (markovBanditHistorySnocGeneral (k := k) (n := n) (S := S)) :=
  measurable_markovBanditSnoc

theorem compProd_fixedActionStepKernel_map_snoc
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (mu : Measure (MarkovBanditHistory k S n))
    [SFinite mu] (i : Fin k) :
    (mu.compProd (markovBanditFixedActionStepKernel P pi i)).map
        markovBanditHistorySnocGeneral =
      (((mu.withDensity (markovBanditSelectMass pi i)).compProd
        (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
          ((measurable_pi_apply i).comp measurable_snd))).map
        (markovBanditHistorySnocFixed i)) := by
  let K : Kernel (MarkovBanditHistory k S n) S :=
    P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
      ((measurable_pi_apply i).comp measurable_snd)
  let v := markovBanditSelectMass (n := n) pi i
  let pairI : S → Fin k × S := fun y ↦ (i, y)
  have hv : Measurable v := measurable_markovBanditSelectMass pi i
  have hpair : Measurable pairI := measurable_const.prodMk measurable_id
  have hd : Measurable (Function.uncurry (fun h : MarkovBanditHistory k S n ↦
      fun _ : S ↦ v h)) := hv.comp measurable_fst
  letI : IsSFiniteKernel (K.withDensity (fun h _ ↦ v h)) :=
    ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity K (fun h _ ↦ by
      exact measure_ne_top ((pi.select n) h) {i})
  rw [markovBanditFixedActionStepKernel]
  rw [Measure.compProd_map hpair]
  rw [Measure.compProd_withDensity hd]
  change Measure.map markovBanditHistorySnocGeneral
      (Measure.map (Prod.map id pairI)
        ((mu.compProd K).withDensity (v ∘ Prod.fst))) =
    Measure.map (markovBanditHistorySnocFixed i)
      ((mu.withDensity v).compProd K)
  rw [← withDensity_compProd_left mu K v hv]
  rw [Measure.map_map measurable_markovBanditHistorySnocGeneral
    (measurable_id.prodMap hpair)]
  congr 1

theorem compProd_markovBanditStepKernel_map_snoc_eq_sum_fixed
    {k n : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S)
    (mu : Measure (MarkovBanditHistory k S n)) [SFinite mu] :
    (mu.compProd (markovBanditStepKernel P pi n)).map
        markovBanditHistorySnocGeneral =
      ∑ i : Fin k,
        (((mu.withDensity (markovBanditSelectMass pi i)).compProd
          (P.comap (fun h : MarkovBanditHistory k S n ↦ h.2 i)
            ((measurable_pi_apply i).comp measurable_snd))).map
          (markovBanditHistorySnocFixed i)) := by
  rw [markovBanditStepKernel_eq_sum_fixedAction]
  rw [← Kernel.sum_fintype]
  rw [Measure.compProd_sum_right]
  rw [Measure.map_sum
    measurable_markovBanditHistorySnocGeneral.aemeasurable]
  rw [Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  exact compProd_fixedActionStepKernel_map_snoc P pi mu i

theorem markovBanditMeasure_eq_sum_fixedActionHistoryMeasure
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∀ n : ℕ, markovBanditMeasure P pi x n =
      ∑ a : Fin n → Fin k,
        markovBanditFixedActionHistoryMeasure P pi x a := by
  intro n
  induction n with
  | zero =>
      have h0 := markovBanditFixedActionHistoryMeasure_zero P pi x
      simpa only [Fintype.sum_unique] using h0.symm
  | succ n ih =>
      rw [markovBanditMeasure]
      change ((markovBanditMeasure P pi x n).compProd
        (markovBanditStepKernel P pi n)).map
          markovBanditHistorySnocGeneral = _
      rw [ih]
      rw [← Measure.sum_fintype]
      rw [Measure.compProd_sum_left]
      rw [Measure.map_sum
        measurable_markovBanditHistorySnocGeneral.aemeasurable]
      rw [Measure.sum_fintype]
      simp_rw [compProd_markovBanditStepKernel_map_snoc_eq_sum_fixed]
      simp_rw [← markovBanditFixedActionHistoryMeasure_snoc]
      rw [← Fintype.sum_prod_type']
      let e : ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) :=
        Equiv.prodComm _ _ |>.trans (Fin.snocEquiv (fun _ ↦ Fin k))
      exact Fintype.sum_equiv e _ _ (fun q ↦ by
        change markovBanditFixedActionHistoryMeasure P pi x
            (Fin.snoc q.1 q.2) =
          markovBanditFixedActionHistoryMeasure P pi x (e q)
        rfl)

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm


theorem sum_markovBanditStackActionLikelihood
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (pi : MarkovBanditPolicy k S) (omega : MarkovBanditStackSpace k S) :
    ∀ n : ℕ, ∑ a : Fin n → Fin k,
      markovBanditStackActionLikelihood pi a omega = 1 := by
  intro n
  induction n with
  | zero => simp [markovBanditStackActionLikelihood,
      markovBanditActionLikelihood]
  | succ n ih =>
      let e : ((Fin n → Fin k) × Fin k) ≃ (Fin (n + 1) → Fin k) :=
        Equiv.prodComm _ _ |>.trans (Fin.snocEquiv (fun _ ↦ Fin k))
      rw [← e.sum_comp]
      change (∑ q : (Fin n → Fin k) × Fin k,
        markovBanditStackActionLikelihood pi (Fin.snoc q.1 q.2) omega) = 1
      rw [Fintype.sum_prod_type'
        (fun a : Fin n → Fin k ↦ fun i : Fin k ↦
          markovBanditStackActionLikelihood pi (Fin.snoc a i) omega)]
      change (∑ a : Fin n → Fin k, ∑ i : Fin k,
        markovBanditStackActionLikelihood pi (Fin.snoc a i) omega) = 1
      simp_rw [markovBanditStackActionLikelihood_snoc]
      calc
        (∑ a : Fin n → Fin k, ∑ i : Fin k,
            markovBanditStackActionLikelihood pi a omega *
              (pi.select n) (markovBanditFiniteStackHistory omega a) {i}) =
            ∑ a : Fin n → Fin k,
              markovBanditStackActionLikelihood pi a omega * 1 := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum]
          congr 1
          simpa using MeasureTheory.Measure.sum_measure_singleton
            (s := Finset.univ)
            ((pi.select n) (markovBanditFiniteStackHistory omega a))
        _ = 1 := by simpa using ih

end BanditAlgorithm

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm




end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal

namespace BanditAlgorithm



noncomputable def markovBanditRetirementEnvelope
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (r : S → ℝ) (α : ℝ)
    (omega : MarkovBanditStackSpace k S) (N : ℕ) : ℝ :=
  ∑ i : Fin k, (
    (∑ u ∈ Finset.range (N + 1),
        discountedAbsoluteRewardValue P r α (omega i u)) +
      (∑' t : ℕ, α ^ t) *
        (discountedAbsoluteRewardValue P r α (omega i 0) +
          ∑ v ∈ Finset.range N, |r (omega i (v + 1))|))

lemma integrable_comp_of_map_eq
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (mu : Measure A) (nu : Measure B) (g : A → B)
    (hg : Measurable g) (hmap : mu.map g = nu)
    {f : B → ℝ} (hf : Integrable f nu) :
    Integrable (fun x ↦ f (g x)) mu := by
  have hfmap : Integrable f (mu.map g) := by rwa [hmap]
  exact (integrable_map_measure hfmap.1 hg.aemeasurable).1 hfmap

lemma integrable_discountedAbsoluteRewardValue_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    Integrable (fun omega : MarkovBanditStackSpace k S ↦
      discountedAbsoluteRewardValue P r α (omega i u))
      (markovBanditStackMeasure P x) := by
  exact integrable_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_discountedAbsoluteRewardValue_along_markov
      P hr hα0 hint (x i) u).1

lemma integrable_abs_reward_stack_arm
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (i : Fin k) (u : ℕ) :
    Integrable (fun omega : MarkovBanditStackSpace k S ↦
      |r (omega i u)|) (markovBanditStackMeasure P x) := by
  exact integrable_comp_of_map_eq
    (markovBanditStackMeasure P x) (markovChainMeasure P (x i))
    (fun omega ↦ omega i) (measurable_pi_apply i)
    (map_markovBanditStackMeasure_arm P x i)
    (integrable_markovChain_eval_of_discounted
      P hr hα0 hint (x i) u).abs

theorem integrable_markovBanditRetirementEnvelope
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α)
    (hint : DiscountedRewardIntegrable P r α)
    (x : Fin k → S) (N : ℕ) :
    Integrable (markovBanditRetirementEnvelope P r α · N)
      (markovBanditStackMeasure P x) := by
  unfold markovBanditRetirementEnvelope
  apply MeasureTheory.integrable_finsetSum
  intro i hi
  apply Integrable.add
  · apply MeasureTheory.integrable_finsetSum
    intro u hu
    exact integrable_discountedAbsoluteRewardValue_stack_arm
      P hr hα0 hint x i u
  · apply Integrable.const_mul
    apply Integrable.add
    · exact integrable_discountedAbsoluteRewardValue_stack_arm
        P hr hα0 hint x i 0
    · apply MeasureTheory.integrable_finsetSum
      intro v hv
      exact integrable_abs_reward_stack_arm P hr hα0 hint x i (v + 1)

theorem sum_withDensity_markovBanditStackActionLikelihood
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    ∑ a : Fin N → Fin k,
        (markovBanditStackMeasure P x).withDensity
          (markovBanditStackActionLikelihood pi a) =
      markovBanditStackMeasure P x := by
  rw [← Measure.sum_fintype, ← withDensity_tsum]
  · rw [show (∑' a : Fin N → Fin k,
        markovBanditStackActionLikelihood pi a) = fun _ ↦ 1 by
      funext omega
      rw [tsum_fintype]
      simpa only [Finset.sum_apply] using
        sum_markovBanditStackActionLikelihood pi omega N]
    simp
  · intro a
    exact measurable_markovBanditStackActionLikelihood pi a

theorem markovBanditExpectedRetirementPotential_le_envelope
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (pi : MarkovBanditPolicy k S) (x : Fin k → S) :
    markovBanditExpectedRetirementPotential P r α pi x N ≤
      ∫ omega, markovBanditRetirementEnvelope P r α omega N
        ∂markovBanditStackMeasure P x := by
  let M := markovBanditStackMeasure P x
  let L := fun (a : Fin N → Fin k) ↦
    markovBanditStackActionLikelihood pi a
  let Q := fun h : MarkovBanditHistory k S N ↦
    currentGittinsRetirementPotential P r α h
  let E := fun omega : MarkovBanditStackSpace k S ↦
    markovBanditRetirementEnvelope P r α omega N
  have hQmeas : Measurable Q := by
    exact (gittins_terminal_potential_regular (k := k)
      P hr hα0 hα1 hint N).1
  have hQint : Integrable Q (markovBanditMeasure P pi x N) := by
    exact (gittins_terminal_potential_regular (k := k)
      P hr hα0 hα1 hint N).2 pi x
  have hEint : Integrable E M :=
    integrable_markovBanditRetirementEnvelope P hr hα0 hint x N
  have hmeasure : ∑ a : Fin N → Fin k, M.withDensity (L a) = M := by
    exact sum_withDensity_markovBanditStackActionLikelihood P pi x
  have hmeasureSum : (Measure.sum fun a : Fin N → Fin k ↦
      M.withDensity (L a)) = M := by
    rw [Measure.sum_fintype]
    exact hmeasure
  have hEa : ∀ a : Fin N → Fin k, Integrable E (M.withDensity (L a)) := by
    intro a
    apply hEint.mono_measure
    exact (Measure.le_sum
      (fun b : Fin N → Fin k ↦ M.withDensity (L b)) a).trans_eq hmeasureSum
  have hfixed : markovBanditExpectedRetirementPotential P r α pi x N =
      ∑ a : Fin N → Fin k,
        ∫ omega, Q (markovBanditFiniteStackHistory omega a)
          ∂M.withDensity (L a) := by
    rw [markovBanditExpectedRetirementPotential]
    change (∫ h, Q h ∂markovBanditMeasure P pi x N) = _
    rw [markovBanditMeasure_eq_sum_fixedActionHistoryMeasure]
    rw [← Measure.sum_fintype]
    have hQsum : Integrable Q
        (Measure.sum fun a : Fin N → Fin k ↦
          markovBanditFixedActionHistoryMeasure P pi x a) := by
      rw [Measure.sum_fintype,
        ← markovBanditMeasure_eq_sum_fixedActionHistoryMeasure]
      exact hQint
    rw [integral_sum_measure hQsum]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a ha
    rw [markovBanditFixedActionHistoryMeasure]
    have hm : Measurable (fun omega : MarkovBanditStackSpace k S ↦
        markovBanditFiniteStackHistory omega a) :=
      measurable_markovBanditFiniteStackHistory.comp
        (measurable_id.prodMk measurable_const)
    rw [integral_map hm.aemeasurable hQmeas.aestronglyMeasurable]
  rw [hfixed]
  calc
    (∑ a : Fin N → Fin k,
        ∫ omega, Q (markovBanditFiniteStackHistory omega a)
          ∂M.withDensity (L a)) ≤
        ∑ a : Fin N → Fin k, ∫ omega, E omega ∂M.withDensity (L a) := by
      apply Finset.sum_le_sum
      intro a ha
      apply integral_mono
      · have hfixedMeasureSum :
            (Measure.sum fun b : Fin N → Fin k ↦
              markovBanditFixedActionHistoryMeasure P pi x b) =
              markovBanditMeasure P pi x N := by
          rw [Measure.sum_fintype]
          exact (markovBanditMeasure_eq_sum_fixedActionHistoryMeasure
            P pi x N).symm
        have hQfixed := hQint.mono_measure
          ((Measure.le_sum
            (fun b : Fin N → Fin k ↦
              markovBanditFixedActionHistoryMeasure P pi x b) a).trans_eq
                hfixedMeasureSum)
        have hm : Measurable (fun omega : MarkovBanditStackSpace k S ↦
            markovBanditFiniteStackHistory omega a) :=
          measurable_markovBanditFiniteStackHistory.comp
            (measurable_id.prodMk measurable_const)
        have hQmap : Integrable Q
            ((M.withDensity (L a)).map
              (fun omega ↦ markovBanditFiniteStackHistory omega a)) := by
          simpa [M, L, markovBanditFixedActionHistoryMeasure] using hQfixed
        exact (integrable_map_measure hQmap.1 hm.aemeasurable).1 hQmap
      · exact hEa a
      · intro omega
        exact gittins_current_terminal_potential_le_stack_envelope
          P hr hα0 hα1 hint omega a
    _ = ∫ omega, E omega ∂M := by
      rw [← integral_finsetSum_measure (fun a _ ↦ hEa a)]
      rw [hmeasure]

end BanditAlgorithm

open MeasureTheory ProbabilityTheory ENNReal


theorem solution
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (π : BanditAlgorithm.MarkovBanditPolicy k S) (x : Fin k → S) :
    let absoluteValue := fun y : S ↦
      ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
        ∂BanditAlgorithm.markovChainMeasure P y
    let envelope := fun (ω : Fin k → ℕ → S) ↦ ∑ i : Fin k,
      ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
        (∑' t : ℕ, α ^ t) *
          (absoluteValue (ω i 0) +
            ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
    let stackMeasure : Measure (Fin k → ℕ → S) :=
      Measure.pi (fun i ↦ BanditAlgorithm.markovChainMeasure P (x i))
    BanditAlgorithm.markovBanditExpectedRetirementPotential P r α π x N ≤
      ∫ ω, envelope ω ∂stackMeasure := by
  change BanditAlgorithm.markovBanditExpectedRetirementPotential P r α π x N ≤
    ∫ ω, BanditAlgorithm.markovBanditRetirementEnvelope P r α ω N
      ∂BanditAlgorithm.markovBanditStackMeasure P x
  exact BanditAlgorithm.markovBanditExpectedRetirementPotential_le_envelope
    P hr hα0 hα1 hint π x
