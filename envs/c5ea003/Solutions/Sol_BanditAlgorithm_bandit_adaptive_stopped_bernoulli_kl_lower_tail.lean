-- Prove2me | solution 1 for BanditAlgorithm.bandit_adaptive_stopped_bernoulli_kl_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T05:53:44.89164+00:00
-- url     : https://prove2.me/submissions/a9041dc4-c99a-47cd-95b0-3cbcb086cf7a

import Definitions.Def_ucbStoppedCenteredSum
import Definitions.Def_banditHistoryPrefix
import Definitions.Def_bernoulliRelativeEntropy
import Theorems.Thm_BanditAlgorithm_bernoulliRelativeEntropy_antitone_fst
import Mathlib.Data.Fintype.Order
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open Filter

/-!
Canonical-model stopped-reward concentration for an arbitrary (possibly
randomized) bandit policy.  This is the reward-stack / bounded optional
stopping bridge from Lattimore--Szepesvári §4.6, Exercise 4.4, used in the
proofs of Theorems 7.1 and 8.1.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def klFstExpandedAst (q p : ℝ) : ℝ :=
  p * Real.log p + (1 - p) * Real.log (1 - p) -
    p * Real.log q - (1 - p) * Real.log (1 - q)

private theorem klFstExpandedAst_eq
    {p q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    klFstExpandedAst q p = bernoulliRelativeEntropy p q := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [klFstExpandedAst, bernoulliRelativeEntropy]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klFstExpandedAst, bernoulliRelativeEntropy]
  rw [klFstExpandedAst, bernoulliRelativeEntropy,
    Real.log_div hp0 (ne_of_gt hq.1),
    Real.log_div (sub_ne_zero.mpr hp1.symm)
      (sub_ne_zero.mpr (ne_of_lt hq.2).symm)]
  ring

private theorem continuous_bernoulliRelativeEntropy_fst_ast
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Continuous (fun p ↦ bernoulliRelativeEntropy p q) := by
  have hcont : Continuous (klFstExpandedAst q) := by
    unfold klFstExpandedAst
    have h1 : Continuous (fun p : ℝ ↦ p * Real.log p) :=
      Real.continuous_mul_log
    have h2 : Continuous (fun p : ℝ ↦
        (1 - p) * Real.log (1 - p)) :=
      Real.continuous_mul_log.comp
        (continuous_const.sub continuous_id)
    fun_prop
  convert hcont using 1
  funext p
  exact (klFstExpandedAst_eq hq).symm

private theorem bernoulliRelativeEntropy_self_ast
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    bernoulliRelativeEntropy q q = 0 := by
  rcases eq_or_ne q 0 with rfl | hq0
  · simp [bernoulliRelativeEntropy]
  rcases eq_or_ne q 1 with rfl | hq1
  · simp [bernoulliRelativeEntropy]
  have hOneQ : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.symm
  simp [bernoulliRelativeEntropy, div_self hq0, div_self hOneQ]

private theorem armPullCount_snoc_ast {k n : ℕ} (i : Fin k)
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    armPullCount i (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armPullCount i h + if z.1 = i then 1 else 0 := by
  apply Nat.cast_injective (R := ℝ)
  rw [Nat.cast_add]
  simp only [armPullCount]
  have hset (g : BanditHistory k n) :
      ({t | (g t).1 = i}.toFinset.card : ℝ) =
        ∑ t, if (g t).1 = i then 1 else 0 := by
    have hs : {t | (g t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (g t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (g t).1 = i)
        Finset.univ).symm
  rw [hset]
  have hsnoc :
      (({t |
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset.card :
          ℕ) : ℝ) =
        ∑ t, if
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i
        then 1 else 0 := by
    have hs : {t |
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i}.toFinset =
        Finset.univ.filter
          (fun t ↦
            (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ)
        (fun t : Fin (n + 1) ↦
          (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z t).1 = i)
        Finset.univ).symm
  rw [hsnoc, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

private theorem measurable_armPullCount_cast_ast {k n : ℕ} (i : Fin k) :
    Measurable (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) := by
  rw [show (fun h : BanditHistory k n ↦ (armPullCount i h : ℝ)) =
      fun h ↦ ∑ t, if (h t).1 = i then (1 : ℝ) else 0 by
    funext h
    rw [armPullCount]
    have hs : {t | (h t).1 = i}.toFinset =
        Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp
    rw [hs]
    simpa using
      (Finset.sum_boole (R := ℝ) (fun t : Fin n ↦ (h t).1 = i)
        Finset.univ).symm]
  apply Finset.measurable_sum
  intro t ht
  have ha : Measurable (fun h : BanditHistory k n ↦ (h t).1) :=
    measurable_fst.comp (measurable_pi_apply t)
  exact Measurable.ite ((measurableSet_singleton i).preimage ha)
    measurable_const measurable_const

private theorem measurable_stoppedScoreFactor_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)) := by
  apply Measurable.exp
  have hcount : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) :=
    (measurable_armPullCount_cast_ast i).comp measurable_fst
  have hlt : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        armPullCount i p.1 < u} := by
    simpa only [Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const : Measurable
        (fun _ : BanditHistory k m × (Fin k × ℝ) ↦ (u : ℝ)))
  have heq : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  exact Measurable.ite (hlt.inter heq)
    ((measurable_snd.snd.sub measurable_const).const_mul t
      |>.sub measurable_const)
    measurable_const

private theorem integrable_banditStepKernel_stoppedScoreFactor_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦ Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_stoppedScoreFactor_ast ν i u t).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    by_cases hc : armPullCount i h < u ∧ a = i
    · have hlt := hc.1
      have hai := hc.2
      subst a
      simp only [Function.comp_apply, id_eq, hlt, and_self, if_pos]
      rw [show (banditRewardKernel ν) i = ν.P i by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      change Integrable
        (fun y : ℝ ↦ Real.exp
          (t * (y - banditArmMean ν i) - t ^ 2 / 8)) (ν.P i)
      have hbase :=
        (hν.2 i).integrable_exp_mul t |>.mul_const
          (Real.exp (-(t ^ 2 / 8)))
      convert hbase using 1
      funext y
      rw [← Real.exp_add]
      congr 1
    · simp [hc]
  · exact Integrable.of_finite

private theorem banditStepKernel_integral_stoppedScoreFactor_le_one_ast
    {k m : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) (π : BanditPolicy k)
    (h : BanditHistory k m) (i : Fin k) (u : ℕ) (t : ℝ) :
    ∫ z : Fin k × ℝ, Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  have hint :=
    integrable_banditStepKernel_stoppedScoreFactor_ast
      ν hν π h i u t
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp
        (if armPullCount i h < u ∧ a = i then
          t * (y - banditArmMean ν i) - t ^ 2 / 8 else 0)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) ≤
        ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      by_cases hc : armPullCount i h < u ∧ a = i
      · have hlt := hc.1
        have hai := hc.2
        subst a
        simp only [hlt, and_self, if_pos]
        rw [show (banditRewardKernel ν) i = ν.P i by
          simp [banditRewardKernel, Kernel.ofFunOfCountable]]
        have hm := (hν.2 i).mgf_le t
        rw [mgf] at hm
        have hm' :
            (∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i) ≤
              Real.exp (t ^ 2 / 8) := by
          convert hm using 1 <;> norm_num <;> ring_nf
        calc
          (∫ y, Real.exp
              (t * (y - banditArmMean ν i) - t ^ 2 / 8) ∂ν.P i) =
              Real.exp (-(t ^ 2 / 8)) *
                ∫ y, Real.exp (t * (y - banditArmMean ν i)) ∂ν.P i := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with y
            rw [← Real.exp_add]
            congr 1
            ring
          _ ≤ Real.exp (-(t ^ 2 / 8)) * Real.exp (t ^ 2 / 8) :=
            mul_le_mul_of_nonneg_left hm' (Real.exp_nonneg _)
          _ = 1 := by
            rw [← Real.exp_add]
            ring_nf
            simp
      · simp [hc]
    _ = 1 := by simp

private theorem armStoppedCenteredSum_snoc_ast {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedCenteredSum ν i u (m + 1)
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedCenteredSum ν i u m h +
        if armPullCount i h < u ∧ z.1 = i then
          z.2 - banditArmMean ν i
        else 0 := by
  simp [armStoppedCenteredSum]

private theorem min_armPullCount_snoc_ast {k m : ℕ}
    (i : Fin k) (u : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    min (armPullCount i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z)) u =
      min (armPullCount i h) u +
        if armPullCount i h < u ∧ z.1 = i then 1 else 0 := by
  rw [armPullCount_snoc_ast]
  by_cases hi : z.1 = i
  · by_cases hlt : armPullCount i h < u
    · simp [hi, hlt]
      omega
    · simp [hi, hlt]
      omega
  · simp [hi]

private theorem measurable_armStoppedCenteredSum_ast {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (m : ℕ) :
    Measurable (armStoppedCenteredSum ν i u m) := by
  induction m with
  | zero => simp [armStoppedCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcount : Measurable (fun h : BanditHistory k (m + 1) ↦
          (armPullCount i (Fin.init h) : ℝ)) :=
        (measurable_armPullCount_cast_ast i).comp hinit
      have hlt : MeasurableSet {h : BanditHistory k (m + 1) |
          armPullCount i (Fin.init h) < u} := by
        simpa only [Nat.cast_lt] using
          measurableSet_lt hcount
            (measurable_const : Measurable
              (fun _ : BanditHistory k (m + 1) ↦ (u : ℝ)))
      have heq : MeasurableSet {h : BanditHistory k (m + 1) |
          (h (Fin.last m)).1 = i} :=
        (measurableSet_singleton i).preimage hlast.fst
      change Measurable (fun h : BanditHistory k (m + 1) ↦
        armStoppedCenteredSum ν i u m (Fin.init h) +
          if armPullCount i (Fin.init h) < u ∧
              (h (Fin.last m)).1 = i then
            (h (Fin.last m)).2 - banditArmMean ν i else 0)
      exact (ih.comp hinit).add
        (Measurable.ite (hlt.inter heq)
          (hlast.snd.sub measurable_const) measurable_const)

private noncomputable def armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) : ℝ :=
  Real.exp (t * armStoppedCenteredSum ν i u m h -
    t ^ 2 / 8 * ((min (armPullCount i h) u : ℕ) : ℝ))

private theorem measurable_armStoppedExpScoreAst {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ) :
    Measurable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) := by
  apply Measurable.exp
  apply
    (measurable_const.mul (measurable_armStoppedCenteredSum_ast ν i u m)).sub
  have hmin : Measurable (fun h : BanditHistory k m ↦
      min (armPullCount i h : ℝ) (u : ℝ)) :=
    (measurable_armPullCount_cast_ast i).min measurable_const
  simpa only [Nat.cast_min] using measurable_const.mul hmin

private theorem armStoppedExpScoreAst_snoc {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (u : ℕ) (t : ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedExpScoreAst ν i u t
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedExpScoreAst ν i u t h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0) := by
  rw [armStoppedExpScoreAst, armStoppedExpScoreAst,
    armStoppedCenteredSum_snoc_ast, min_armPullCount_snoc_ast, Nat.cast_add]
  by_cases hlt : armPullCount i h < u
  · by_cases hi : z.1 = i
    · simp only [hlt, hi, and_self, if_pos, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [hlt, hi]
  · simp [hlt]

private theorem integrable_compProd_armStoppedExpScoreAst_factor
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    {m : ℕ} (μ : Measure (BanditHistory k m)) [IsProbabilityMeasure μ]
    (i : Fin k) (u : ℕ) (t : ℝ)
    (hold : Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armStoppedExpScoreAst ν i u t p.1 * Real.exp
        (if armPullCount i p.1 < u ∧ p.2.1 = i then
          t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armStoppedExpScoreAst ν i u t p.1 * Real.exp
      (if armPullCount i p.1 < u ∧ p.2.1 = i then
        t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armStoppedExpScoreAst ν i u t).comp measurable_fst).mul
      (measurable_stoppedScoreFactor_ast ν i u t)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_stoppedScoreFactor_ast
        ν hν π h i u t).const_mul
          (armStoppedExpScoreAst ν i u t h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ armStoppedExpScoreAst ν i u t h :=
      Real.exp_nonneg _
    have hcond :=
      banditStepKernel_integral_stoppedScoreFactor_le_one_ast
        ν hν π h i u t
    have hinner_nonneg :
        0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖armStoppedExpScoreAst ν i u t h * Real.exp
      (if armPullCount i h < u ∧ z.1 = i then
        t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖armStoppedExpScoreAst ν i u t h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

private theorem armStoppedExpScoreAst_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) (t : ℝ) : ∀ m : ℕ,
    Integrable
      (armStoppedExpScoreAst ν i u t : BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    ∫ h, armStoppedExpScoreAst ν i u t h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;>
        simp [banditMeasure, armStoppedExpScoreAst,
          armStoppedCenteredSum, armPullCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc :
          BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        armStoppedExpScoreAst ν i u t p.1 * Real.exp
          (if armPullCount i p.1 < u ∧ p.2.1 = i then
            t * (p.2.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
      have hrewrite :
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p)) = F := by
        funext p
        exact armStoppedExpScoreAst_snoc ν i u t p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_armStoppedExpScoreAst_factor
          ν hν μ i u t ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armStoppedExpScoreAst
            (m := m + 1) ν i u t).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable
          (fun p ↦ armStoppedExpScoreAst ν i u t (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armStoppedExpScoreAst
              (m := m + 1) ν i u t).aestronglyMeasurable]
        change (∫ p, armStoppedExpScoreAst ν i u t (snoc p)
          ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, armStoppedExpScoreAst ν i u t h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, armStoppedExpScoreAst ν i u t h * Real.exp
              (if armPullCount i h < u ∧ z.1 = i then
                t * (z.2 - banditArmMean ν i) - t ^ 2 / 8 else 0)
              ∂κ h) ≤ armStoppedExpScoreAst ν i u t h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_stoppedScoreFactor_le_one_ast
                ν hν π h i u t)
          _ ≤ 1 := ih.2

theorem adaptive_armStoppedCenteredSum_upper_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (4 * t) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (4 * t) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        (u : ℝ) * t ≤ armStoppedCenteredSum ν i u n h} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

theorem adaptive_armStoppedCenteredSum_lower_tail_half
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit (1 / 2) ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
      Real.exp (-2 * (u : ℝ) * t ^ 2) := by
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    -armStoppedCenteredSum ν i u n h -
      t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedExpScoreAst_integrable_and_integral_le_one
      ν hν (π := π) i u (-(4 * t)) n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) =
      armStoppedExpScoreAst ν i u (-(4 * t)) := by
    funext h
    rw [armStoppedExpScoreAst]
    dsimp [X]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((4 * t) * X h)) μ := by
    rw [hexp]
    exact hscore.1
  have h4t : 0 ≤ 4 * t := mul_nonneg (by norm_num) ht
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * t / 2) h4t hint
  calc
    μ.real {h : BanditHistory k n |
        armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t} ≤
        μ.real {h | (u : ℝ) * t / 2 ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : ((min (armPullCount i h) u : ℕ) : ℝ) ≤ u := by
        exact_mod_cast Nat.min_le_right (armPullCount i h) u
      have hmul : 0 ≤ t *
          ((u : ℝ) - ((min (armPullCount i h) u : ℕ) : ℝ)) :=
        mul_nonneg ht (sub_nonneg.mpr hmin)
      dsimp [X]
      change armStoppedCenteredSum ν i u n h ≤ -(u : ℝ) * t at hh
      have hh' : (u : ℝ) * t ≤
          -armStoppedCenteredSum ν i u n h := by
        linarith
      have hbase : (u : ℝ) * t / 2 ≤ (u : ℝ) * t -
          t / 2 * ((min (armPullCount i h) u : ℕ) : ℝ) := by
        nlinarith [hmul]
      exact hbase.trans (sub_le_sub_right hh' _)
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) *
          mgf X μ (4 * t) := hchern
    _ ≤ Real.exp (-(4 * t) * ((u : ℝ) * t / 2)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf, hexp]
        exact hscore.2
      · positivity
    _ = Real.exp (-2 * (u : ℝ) * t ^ 2) := by
      congr 1
      ring

private noncomputable def armCenteredSumAst {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n) : ℝ :=
  ∑ t, if (h t).1 = i then (h t).2 - banditArmMean ν i else 0

private theorem armCenteredSumAst_snoc {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (h : BanditHistory k n)
    (z : Fin k × ℝ) :
    armCenteredSumAst ν i
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armCenteredSumAst ν i h +
        if z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp only [armCenteredSumAst, Fin.sum_univ_castSucc]
  by_cases hz : z.1 = i <;> simp [hz]

theorem armStoppedCenteredSum_eq_pullCount_mul_empirical_sub_mean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (u : ℕ)
    (h : BanditHistory k m) (hcount : armPullCount i h ≤ u) :
    armStoppedCenteredSum ν i u m h =
      (armPullCount i h : ℝ) *
        (armEmpiricalMean i h - banditArmMean ν i) := by
  have hstop :
      armStoppedCenteredSum ν i u m h = armCenteredSumAst ν i h := by
    induction m with
    | zero => simp [armStoppedCenteredSum, armCenteredSumAst]
    | succ m ih =>
        rw [← Fin.snoc_init_self h] at hcount ⊢
        rw [armPullCount_snoc_ast] at hcount
        rw [armStoppedCenteredSum_snoc_ast, armCenteredSumAst_snoc]
        by_cases hi : (h (Fin.last m)).1 = i
        · have hprev : armPullCount i (Fin.init h) < u := by
            simp [hi] at hcount
            omega
          rw [if_pos ⟨hprev, hi⟩, if_pos hi,
            ih (Fin.init h) (Nat.le_of_lt hprev)]
        · have hprev : armPullCount i (Fin.init h) ≤ u := by
            simpa [hi] using hcount
          rw [if_neg (fun hc ↦ hi hc.2), if_neg hi,
            ih (Fin.init h) hprev]
  rw [hstop]
  let S : Finset (Fin m) := {t | (h t).1 = i}.toFinset
  have hsum : (∑ t, if (h t).1 = i then
      (h t).2 - banditArmMean ν i else 0) =
      ∑ t ∈ S, ((h t).2 - banditArmMean ν i) := by
    have hS : S = Finset.univ.filter (fun t ↦ (h t).1 = i) := by
      ext t
      simp [S]
    rw [hS, Finset.sum_filter]
  rw [armCenteredSumAst, hsum]
  change (∑ t ∈ S, ((h t).2 - banditArmMean ν i)) =
    (S.card : ℝ) *
      ((∑ t ∈ S, (h t).2) / (S.card : ℝ) - banditArmMean ν i)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  by_cases hc : S.card = 0
  · have hS0 : S = ∅ := Finset.card_eq_zero.mp hc
    simp [hS0]
  · have hcast : (S.card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp

private theorem measurable_banditHistoryPrefixAt_ast {k n : ℕ}
    (r : Fin n) :
    Measurable
      (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) := by
  rw [measurable_pi_iff]
  intro s
  exact measurable_pi_apply
    (⟨s.val, lt_trans s.isLt r.isLt⟩ : Fin n)

private theorem prefixAt_snoc_castSucc_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) (r : Fin n) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) r.castSucc =
      banditHistoryPrefixAt h r := by
  funext s
  unfold banditHistoryPrefixAt
  have hsr : s.val < r.val := by simpa using s.isLt
  have hsn : s.val < n := lt_trans hsr r.isLt
  rw [Fin.snoc]
  rw [dif_pos hsn]
  simp

private theorem prefixAt_snoc_last_ast {k n : ℕ}
    (h : BanditHistory k n) (z : Fin k × ℝ) :
    banditHistoryPrefixAt
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) (Fin.last n) = h := by
  funext s
  simp [banditHistoryPrefixAt, Fin.snoc]

private theorem banditMeasure_map_init_ast {k m : ℕ}
    (ν : StochasticBandit k) (π : BanditPolicy k) :
    (banditMeasure ν π (m + 1)).map
        (fun h : BanditHistory k (m + 1) ↦ Fin.init h) =
      banditMeasure ν π m := by
  rw [banditMeasure]
  rw [MeasureTheory.Measure.map_map
    (by fun_prop :
      Measurable (fun h : BanditHistory k (m + 1) ↦ Fin.init h))
    measurable_banditHistorySnoc]
  have hfun :
      ((fun h : BanditHistory k (m + 1) ↦ Fin.init h) ∘
        (fun h : BanditHistory k m × (Fin k × ℝ) ↦
          Fin.snoc (α := fun _ ↦ Fin k × ℝ) h.1 h.2)) =
        Prod.fst := by
    funext p
    simp
  rw [hfun]
  change Measure.fst
      ((banditMeasure ν π m).compProd (banditStepKernel ν π m)) =
    banditMeasure ν π m
  exact MeasureTheory.Measure.fst_compProd
    (banditMeasure ν π m) (banditStepKernel ν π m)

theorem banditMeasure_map_historyPrefixAt
    {k n : ℕ} (ν : StochasticBandit k) (π : BanditPolicy k)
    (r : Fin n) :
    (banditMeasure ν π n).map
        (fun h : BanditHistory k n ↦ banditHistoryPrefixAt h r) =
      banditMeasure ν π r.val := by
  induction n with
  | zero => exact Fin.elim0 r
  | succ n ih =>
      refine Fin.lastCases ?_ (fun s ↦ ?_) r
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h (Fin.last n)) =
            banditMeasure ν π n
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h (Fin.last n)) =
          (fun h ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa using
              prefixAt_snoc_last_ast (Fin.init h) (h (Fin.last n))]
        exact banditMeasure_map_init_ast ν π
      · change
          (banditMeasure ν π (n + 1)).map
              (fun h : BanditHistory k (n + 1) ↦
                banditHistoryPrefixAt h s.castSucc) =
            banditMeasure ν π s.val
        rw [show
          (fun h : BanditHistory k (n + 1) ↦
            banditHistoryPrefixAt h s.castSucc) =
          (fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
            (fun h : BanditHistory k (n + 1) ↦ Fin.init h) by
            funext h
            rw [← Fin.snoc_init_self h]
            simpa [Function.comp_apply] using
              prefixAt_snoc_castSucc_ast
                (Fin.init h) (h (Fin.last n)) s]
        calc
          (banditMeasure ν π (n + 1)).map
              ((fun g : BanditHistory k n ↦ banditHistoryPrefixAt g s) ∘
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)) =
              ((banditMeasure ν π (n + 1)).map
                (fun h : BanditHistory k (n + 1) ↦ Fin.init h)).map
                (fun g : BanditHistory k n ↦
                  banditHistoryPrefixAt g s) := by
            symm
            exact MeasureTheory.Measure.map_map
              (measurable_banditHistoryPrefixAt_ast s)
              (by fun_prop :
                Measurable
                  (fun h : BanditHistory k (n + 1) ↦ Fin.init h))
          _ = banditMeasure ν π s.val := by
            rw [banditMeasure_map_init_ast ν π, ih s]

private theorem banditArmMean_bernoulli_kl
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (j : Fin k) :
    banditArmMean ν j = μvec j := by
  rw [hν, banditArmMean, bernoulliBandit]
  change (∫ x : ℝ, x ∂(ENNReal.ofReal (μvec j) • Measure.dirac (1 : ℝ) +
    ENNReal.ofReal (1 - μvec j) • Measure.dirac (0 : ℝ))) = μvec j
  rw [integral_add_measure
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (1 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness) :
      Integrable (fun x : ℝ ↦ x) (Measure.dirac (0 : ℝ))).smul_measure
        ENNReal.ofReal_ne_top)]
  rcases hμ j with ⟨h0, h1⟩
  simp [ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec j by linarith)]

private noncomputable def bernoulliMgfKL (μ lmb : ℝ) : ℝ :=
  1 - μ + μ * Real.exp lmb

private noncomputable def armStoppedBernoulliScoreKL
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (μ : ℝ) (u : ℕ) (lmb : ℝ) (h : BanditHistory k m) : ℝ :=
  Real.exp
    (lmb * (armStoppedCenteredSum ν i u m h +
      banditArmMean ν i *
        ((min (armPullCount i h) u : ℕ) : ℝ)) -
      Real.log (bernoulliMgfKL μ lmb) *
        ((min (armPullCount i h) u : ℕ) : ℝ))

private theorem measurable_armStoppedBernoulliScoreKL
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (μ : ℝ) (u : ℕ) (lmb : ℝ) :
    Measurable
      (armStoppedBernoulliScoreKL ν i μ u lmb :
        BanditHistory k m → ℝ) := by
  apply Measurable.exp
  have hmin : Measurable (fun h : BanditHistory k m ↦
      min (armPullCount i h : ℝ) (u : ℝ)) :=
    (measurable_armPullCount_cast_ast i).min measurable_const
  have hmin' : Measurable (fun h : BanditHistory k m ↦
      ((min (armPullCount i h) u : ℕ) : ℝ)) := by
    simpa only [Nat.cast_min] using hmin
  exact (measurable_const.mul
      ((measurable_armStoppedCenteredSum_ast ν i u m).add
        (measurable_const.mul hmin'))).sub
    (measurable_const.mul hmin')

private theorem armStoppedBernoulliScoreKL_snoc
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (μ : ℝ) (u : ℕ) (lmb : ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    armStoppedBernoulliScoreKL ν i μ u lmb
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      armStoppedBernoulliScoreKL ν i μ u lmb h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          lmb * z.2 - Real.log (bernoulliMgfKL μ lmb) else 0) := by
  rw [armStoppedBernoulliScoreKL, armStoppedBernoulliScoreKL,
    armStoppedCenteredSum_snoc_ast, min_armPullCount_snoc_ast, Nat.cast_add]
  by_cases hlt : armPullCount i h < u
  · by_cases hi : z.1 = i
    · simp only [hlt, hi, and_self, if_pos, Nat.cast_one]
      rw [← Real.exp_add]
      congr 1
      ring
    · simp [hlt, hi]
  · simp [hlt]

private theorem measurable_bernoulliFactorKL
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k)
    (μ : ℝ) (u : ℕ) (lmb : ℝ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      Real.exp (if armPullCount i p.1 < u ∧ p.2.1 = i then
        lmb * p.2.2 - Real.log (bernoulliMgfKL μ lmb) else 0)) := by
  apply Measurable.exp
  have hcount : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (armPullCount i p.1 : ℝ)) :=
    (measurable_armPullCount_cast_ast i).comp measurable_fst
  have hlt : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) |
        armPullCount i p.1 < u} := by
    simpa only [Nat.cast_lt] using measurableSet_lt hcount
      (measurable_const :
        Measurable (fun _ : BanditHistory k m × (Fin k × ℝ) ↦ (u : ℝ)))
  have heq : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} :=
    (measurableSet_singleton i).preimage measurable_snd.fst
  exact Measurable.ite (hlt.inter heq)
    (measurable_const.mul measurable_snd.snd |>.sub measurable_const)
    measurable_const

private theorem bernoulliMgfKL_pos
    {μ lmb : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    0 < bernoulliMgfKL μ lmb := by
  unfold bernoulliMgfKL
  by_cases hμ1 : μ = 1
  · simpa [hμ1] using Real.exp_pos lmb
  · have hlt : μ < 1 := lt_of_le_of_ne hμ.2 hμ1
    have hfirst : 0 < 1 - μ := sub_pos.mpr hlt
    have hsecond : 0 ≤ μ * Real.exp lmb :=
      mul_nonneg hμ.1 (Real.exp_pos _).le
    linarith

private theorem integrable_bernoulli_exp_factor_kl
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (i : Fin k) (lmb : ℝ) :
    Integrable (fun y : ℝ ↦ Real.exp
      (lmb * y - Real.log (bernoulliMgfKL (μvec i) lmb)))
      (ν.P i) := by
  rw [hν, bernoulliBandit]
  apply Integrable.add_measure
  · exact (integrable_dirac (by finiteness)).smul_measure
      ENNReal.ofReal_ne_top
  · exact (integrable_dirac (by finiteness)).smul_measure
      ENNReal.ofReal_ne_top

private theorem integral_bernoulli_exp_factor_eq_one_kl
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (i : Fin k) (lmb : ℝ) :
    (∫ y : ℝ, Real.exp
      (lmb * y - Real.log (bernoulliMgfKL (μvec i) lmb))
      ∂ν.P i) = 1 := by
  have hint :=
    integrable_bernoulli_exp_factor_kl μvec hμ ν hν i lmb
  rw [hν, bernoulliBandit] at hint ⊢
  rw [integral_add_measure
    ((integrable_dirac (by finiteness)).smul_measure
      ENNReal.ofReal_ne_top)
    ((integrable_dirac (by finiteness)).smul_measure
      ENNReal.ofReal_ne_top)]
  have hμ0 := (hμ i).1
  have hμ1 := (hμ i).2
  have hMpos : 0 < bernoulliMgfKL (μvec i) lmb :=
    bernoulliMgfKL_pos (hμ i)
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal hμ0,
    ENNReal.toReal_ofReal (show 0 ≤ 1 - μvec i by linarith)]
  calc
    μvec i * Real.exp
          (lmb * 1 - Real.log (bernoulliMgfKL (μvec i) lmb)) +
        (1 - μvec i) * Real.exp
          (lmb * 0 - Real.log (bernoulliMgfKL (μvec i) lmb)) =
      Real.exp (-Real.log (bernoulliMgfKL (μvec i) lmb)) *
        bernoulliMgfKL (μvec i) lmb := by
      rw [show Real.exp
          (lmb * 1 - Real.log (bernoulliMgfKL (μvec i) lmb)) =
        Real.exp (-Real.log (bernoulliMgfKL (μvec i) lmb)) *
          Real.exp lmb by
            rw [← Real.exp_add]
            congr 1
            ring]
      simp only [mul_zero, zero_sub]
      rw [bernoulliMgfKL]
      ring
    _ = 1 := by
      rw [Real.exp_neg, Real.exp_log hMpos]
      field_simp [ne_of_gt hMpos]

private theorem integrable_banditStepKernel_bernoulliFactorKL
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (i : Fin k) (u : ℕ) (lmb : ℝ) :
    Integrable (fun z : Fin k × ℝ ↦
      Real.exp (if armPullCount i h < u ∧ z.1 = i then
        lmb * z.2 - Real.log (bernoulliMgfKL (μvec i) lmb) else 0))
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_bernoulliFactorKL ν i (μvec i) u lmb).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    by_cases hc : armPullCount i h < u ∧ a = i
    · have hlt := hc.1
      have hai := hc.2
      subst a
      simp only [Function.comp_apply, id_eq, hlt, and_self, if_pos]
      rw [show (banditRewardKernel ν) i = ν.P i by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      exact integrable_bernoulli_exp_factor_kl μvec hμ ν hν i lmb
    · simp [hc]
  · exact Integrable.of_finite

private theorem banditStepKernel_integral_bernoulliFactor_eq_one_KL
    {k m : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (i : Fin k) (u : ℕ) (lmb : ℝ) :
    (∫ z : Fin k × ℝ,
      Real.exp (if armPullCount i h < u ∧ z.1 = i then
        lmb * z.2 - Real.log (bernoulliMgfKL (μvec i) lmb) else 0)
      ∂banditStepKernel ν π m h) = 1 := by
  have hint :=
    integrable_banditStepKernel_bernoulliFactorKL
      μvec hμ ν hν π h i u lmb
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp
        (if armPullCount i h < u ∧ a = i then
          lmb * y - Real.log (bernoulliMgfKL (μvec i) lmb) else 0)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) =
        ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_congr_ae
      filter_upwards with a
      rw [Kernel.comap_apply]
      by_cases hc : armPullCount i h < u ∧ a = i
      · have hlt := hc.1
        have hai := hc.2
        subst a
        simp only [hlt, and_self, if_pos]
        rw [show (banditRewardKernel ν) i = ν.P i by
          simp [banditRewardKernel, Kernel.ofFunOfCountable]]
        exact integral_bernoulli_exp_factor_eq_one_kl
          μvec hμ ν hν i lmb
      · simp [hc]
    _ = 1 := by simp

private theorem integrable_compProd_armStoppedBernoulliScoreKL_factor
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k}
    {m : ℕ} (μhist : Measure (BanditHistory k m))
    [IsProbabilityMeasure μhist]
    (i : Fin k) (u : ℕ) (lmb : ℝ)
    (hold : Integrable
      (armStoppedBernoulliScoreKL ν i (μvec i) u lmb :
        BanditHistory k m → ℝ) μhist) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      armStoppedBernoulliScoreKL ν i (μvec i) u lmb p.1 *
        Real.exp (if armPullCount i p.1 < u ∧ p.2.1 = i then
          lmb * p.2.2 -
            Real.log (bernoulliMgfKL (μvec i) lmb) else 0))
      (μhist.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    armStoppedBernoulliScoreKL ν i (μvec i) u lmb p.1 *
      Real.exp (if armPullCount i p.1 < u ∧ p.2.1 = i then
        lmb * p.2.2 -
          Real.log (bernoulliMgfKL (μvec i) lmb) else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_armStoppedBernoulliScoreKL
        ν i (μvec i) u lmb).comp measurable_fst).mul
      (measurable_bernoulliFactorKL ν i (μvec i) u lmb)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_banditStepKernel_bernoulliFactorKL
        μvec hμ ν hν π h i u lmb).const_mul
          (armStoppedBernoulliScoreKL ν i (μvec i) u lmb h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore :
        0 ≤ armStoppedBernoulliScoreKL ν i (μvec i) u lmb h :=
      Real.exp_nonneg _
    have hcond :=
      banditStepKernel_integral_bernoulliFactor_eq_one_KL
        μvec hμ ν hν π h i u lmb
    have hinner_nonneg :
        0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z,
      ‖armStoppedBernoulliScoreKL ν i (μvec i) u lmb h *
        Real.exp (if armPullCount i h < u ∧ z.1 = i then
          lmb * z.2 -
            Real.log (bernoulliMgfKL (μvec i) lmb) else 0)‖
      ∂banditStepKernel ν π m h) ≤
        ‖armStoppedBernoulliScoreKL ν i (μvec i) u lmb h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul, hcond, mul_one]

private theorem armStoppedBernoulliScoreKL_integrable_and_integral_eq_one
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k} (i : Fin k) (u : ℕ) (lmb : ℝ) :
    ∀ m : ℕ,
    Integrable
      (armStoppedBernoulliScoreKL ν i (μvec i) u lmb :
        BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    (∫ h, armStoppedBernoulliScoreKL ν i (μvec i) u lmb h
      ∂banditMeasure ν π m) = 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;>
        simp [banditMeasure, armStoppedBernoulliScoreKL,
          armStoppedCenteredSum, armPullCount]
  | succ m ih =>
      let μhist := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc :
          BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        armStoppedBernoulliScoreKL ν i (μvec i) u lmb p.1 *
          Real.exp (if armPullCount i p.1 < u ∧ p.2.1 = i then
            lmb * p.2.2 -
              Real.log (bernoulliMgfKL (μvec i) lmb) else 0)
      have hrewrite :
          (fun p ↦ armStoppedBernoulliScoreKL ν i (μvec i) u lmb
            (snoc p)) = F := by
        funext p
        exact armStoppedBernoulliScoreKL_snoc
          ν i (μvec i) u lmb p.1 p.2
      have hcomp : Integrable F (μhist.compProd κ) :=
        integrable_compProd_armStoppedBernoulliScoreKL_factor
          μvec hμ ν hν μhist i u lmb ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_armStoppedBernoulliScoreKL
            (m := m + 1) ν i (μvec i) u lmb).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable
          (fun p ↦ armStoppedBernoulliScoreKL
            ν i (μvec i) u lmb (snoc p))
          (μhist.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_armStoppedBernoulliScoreKL
              (m := m + 1) ν i (μvec i) u lmb).aestronglyMeasurable]
        change (∫ p, armStoppedBernoulliScoreKL
          ν i (μvec i) u lmb (snoc p)
          ∂(μhist.compProd κ)) = 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μhist) =
              ∫ h, armStoppedBernoulliScoreKL
                ν i (μvec i) u lmb h ∂μhist := by
            apply integral_congr_ae
            filter_upwards [] with h
            change (∫ z,
              armStoppedBernoulliScoreKL ν i (μvec i) u lmb h *
                Real.exp (if armPullCount i h < u ∧ z.1 = i then
                  lmb * z.2 -
                    Real.log (bernoulliMgfKL (μvec i) lmb) else 0)
              ∂κ h) =
                armStoppedBernoulliScoreKL ν i (μvec i) u lmb h
            rw [integral_const_mul,
              banditStepKernel_integral_bernoulliFactor_eq_one_KL
                μvec hμ ν hν π h i u lmb,
              mul_one]
          _ = 1 := ih.2

private theorem bernoulli_tilt_identity_KL
    {μ r : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hr0 : 0 < r) (hrμ : r < μ) :
    let lmb := Real.log (r * (1 - μ) / (μ * (1 - r)))
    lmb * r - Real.log (bernoulliMgfKL μ lmb) =
      bernoulliRelativeEntropy r μ := by
  dsimp only
  have hOneMu : 0 < 1 - μ := sub_pos.mpr hμ1
  have hOneR : 0 < 1 - r := sub_pos.mpr (hrμ.trans hμ1)
  have hratio :
      0 < r * (1 - μ) / (μ * (1 - r)) :=
    div_pos (mul_pos hr0 hOneMu) (mul_pos hμ0 hOneR)
  have hmgf :
      bernoulliMgfKL μ
          (Real.log (r * (1 - μ) / (μ * (1 - r)))) =
        (1 - μ) / (1 - r) := by
    rw [bernoulliMgfKL, Real.exp_log hratio]
    field_simp [ne_of_gt hμ0, ne_of_gt hOneR]
    ring
  rw [hmgf, bernoulliRelativeEntropy]
  rw [Real.log_div (mul_ne_zero (ne_of_gt hr0) (ne_of_gt hOneMu))
      (mul_ne_zero (ne_of_gt hμ0) (ne_of_gt hOneR)),
    Real.log_mul (ne_of_gt hr0) (ne_of_gt hOneMu),
    Real.log_mul (ne_of_gt hμ0) (ne_of_gt hOneR),
    Real.log_div (ne_of_gt hOneMu) (ne_of_gt hOneR),
    Real.log_div (ne_of_gt hr0) (ne_of_gt hμ0),
    Real.log_div (ne_of_gt hOneR) (ne_of_gt hOneMu)]
  ring

private theorem adaptive_armStoppedBernoulli_lower_tail_interior_KL
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k} (i : Fin k) (u : ℕ) {r : ℝ}
    (hμ0 : 0 < μvec i) (hμ1 : μvec i < 1)
    (hr0 : 0 < r) (hrμ : r < μvec i) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          u ≤ armPullCount i h ∧
          armStoppedCenteredSum ν i u n h +
              μvec i * (u : ℝ) ≤ (u : ℝ) * r} ≤
      Real.exp (-((u : ℝ) *
        bernoulliRelativeEntropy r (μvec i))) := by
  let μhist := banditMeasure ν π n
  let lmb :=
    Real.log (r * (1 - μvec i) / (μvec i * (1 - r)))
  let X : BanditHistory k n → ℝ := fun h ↦
    lmb * (armStoppedCenteredSum ν i u n h +
      banditArmMean ν i *
        ((min (armPullCount i h) u : ℕ) : ℝ)) -
      Real.log (bernoulliMgfKL (μvec i) lmb) *
        ((min (armPullCount i h) u : ℕ) : ℝ)
  have hscore :=
    armStoppedBernoulliScoreKL_integrable_and_integral_eq_one
      μvec hμ ν hν (π := π) i u lmb n
  have hexp :
      (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h)) =
        armStoppedBernoulliScoreKL ν i (μvec i) u lmb := by
    funext h
    rw [armStoppedBernoulliScoreKL]
    dsimp [X]
    rw [banditArmMean_bernoulli_kl μvec hμ ν hν i]
    congr 1
    ring
  have hint : Integrable
      (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h)) μhist := by
    rw [hexp]
    exact hscore.1
  have hchern := measure_ge_le_exp_mul_mgf
    (μ := μhist) (X := X)
    ((u : ℝ) * bernoulliRelativeEntropy r (μvec i))
    (by norm_num : (0 : ℝ) ≤ 1) hint
  calc
    μhist.real
        {h : BanditHistory k n |
          u ≤ armPullCount i h ∧
          armStoppedCenteredSum ν i u n h +
              μvec i * (u : ℝ) ≤ (u : ℝ) * r} ≤
        μhist.real {h |
          (u : ℝ) * bernoulliRelativeEntropy r (μvec i) ≤ X h} := by
      apply measureReal_mono (h₂ := measure_ne_top _ _)
      intro h hh
      have hmin : min (armPullCount i h) u = u :=
        Nat.min_eq_right hh.1
      have hlmb : lmb < 0 := by
        dsimp [lmb]
        apply Real.log_neg
        · exact div_pos
            (mul_pos hr0 (sub_pos.mpr hμ1))
            (mul_pos hμ0 (sub_pos.mpr (hrμ.trans hμ1)))
        · rw [div_lt_one
            (mul_pos hμ0 (sub_pos.mpr (hrμ.trans hμ1)))]
          nlinarith
      have htilt :
          lmb * r -
              Real.log (bernoulliMgfKL (μvec i) lmb) =
            bernoulliRelativeEntropy r (μvec i) :=
        bernoulli_tilt_identity_KL hμ0 hμ1 hr0 hrμ
      dsimp [X]
      rw [hmin, banditArmMean_bernoulli_kl μvec hμ ν hν i]
      have hmul := mul_le_mul_of_nonpos_left hh.2 hlmb.le
      nlinarith
    _ ≤ Real.exp (-(1 : ℝ) *
          ((u : ℝ) * bernoulliRelativeEntropy r (μvec i))) *
        mgf X μhist 1 := hchern
    _ = Real.exp (-((u : ℝ) *
          bernoulliRelativeEntropy r (μvec i))) := by
      rw [mgf, hexp, hscore.2]
      ring_nf

private theorem bernoulli_entropy_zero_exp_KL
    {u : ℕ} {μ : ℝ} (hμ1 : μ < 1) :
    (1 - μ) ^ u =
      Real.exp (-((u : ℝ) * bernoulliRelativeEntropy 0 μ)) := by
  have hOneMu : 0 < 1 - μ := sub_pos.mpr hμ1
  rw [bernoulliRelativeEntropy]
  norm_num only [zero_div, Real.log_zero, zero_mul, zero_add, one_div,
    one_mul, sub_zero]
  rw [Real.log_inv]
  rw [show -((u : ℝ) * -Real.log (1 - μ)) =
      (u : ℝ) * Real.log (1 - μ) by ring,
    Real.exp_nat_mul, Real.exp_log hOneMu]

private theorem adaptive_armStoppedBernoulli_lower_tail_zero_KL
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k} (i : Fin k) (u : ℕ)
    (hμ1 : μvec i < 1) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          u ≤ armPullCount i h ∧
          armStoppedCenteredSum ν i u n h +
              μvec i * (u : ℝ) ≤ 0} ≤
      Real.exp (-((u : ℝ) *
        bernoulliRelativeEntropy 0 (μvec i))) := by
  let μhist := banditMeasure ν π n
  have hbound (q : ℕ) :
      μhist.real
          {h : BanditHistory k n |
            u ≤ armPullCount i h ∧
            armStoppedCenteredSum ν i u n h +
                μvec i * (u : ℝ) ≤ 0} ≤
        (μvec i * Real.exp (-(q : ℝ)) + (1 - μvec i)) ^ u := by
    let lmb := -(q : ℝ)
    let X : BanditHistory k n → ℝ := fun h ↦
      lmb * (armStoppedCenteredSum ν i u n h +
        banditArmMean ν i *
          ((min (armPullCount i h) u : ℕ) : ℝ)) -
        Real.log (bernoulliMgfKL (μvec i) lmb) *
          ((min (armPullCount i h) u : ℕ) : ℝ)
    have hscore :=
      armStoppedBernoulliScoreKL_integrable_and_integral_eq_one
        μvec hμ ν hν (π := π) i u lmb n
    have hexp :
        (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h)) =
          armStoppedBernoulliScoreKL ν i (μvec i) u lmb := by
      funext h
      rw [armStoppedBernoulliScoreKL]
      dsimp [X]
      rw [banditArmMean_bernoulli_kl μvec hμ ν hν i]
      congr 1
      ring
    have hint : Integrable
        (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h)) μhist := by
      rw [hexp]
      exact hscore.1
    have hchern := measure_ge_le_exp_mul_mgf
      (μ := μhist) (X := X)
      (-((u : ℝ) * Real.log (bernoulliMgfKL (μvec i) lmb)))
      (by norm_num : (0 : ℝ) ≤ 1) hint
    calc
      μhist.real
          {h : BanditHistory k n |
            u ≤ armPullCount i h ∧
            armStoppedCenteredSum ν i u n h +
                μvec i * (u : ℝ) ≤ 0} ≤
          μhist.real {h |
            -((u : ℝ) *
                Real.log (bernoulliMgfKL (μvec i) lmb)) ≤ X h} := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro h hh
        have hmin : min (armPullCount i h) u = u :=
          Nat.min_eq_right hh.1
        have hlmb : lmb ≤ 0 := by
          dsimp [lmb]
          exact neg_nonpos.mpr (Nat.cast_nonneg q)
        have hmul := mul_nonneg_of_nonpos_of_nonpos hlmb hh.2
        dsimp [X]
        rw [hmin, banditArmMean_bernoulli_kl μvec hμ ν hν i]
        nlinarith
      _ ≤ Real.exp (-(1 : ℝ) *
            (-((u : ℝ) *
              Real.log (bernoulliMgfKL (μvec i) lmb)))) *
          mgf X μhist 1 := hchern
      _ = (μvec i * Real.exp (-(q : ℝ)) +
            (1 - μvec i)) ^ u := by
        rw [mgf, hexp, hscore.2, mul_one]
        have hMpos :
            0 < bernoulliMgfKL (μvec i) lmb :=
          bernoulliMgfKL_pos (hμ i)
        rw [show -(1 : ℝ) *
            (-((u : ℝ) *
              Real.log (bernoulliMgfKL (μvec i) lmb))) =
            (u : ℝ) * Real.log (bernoulliMgfKL (μvec i) lmb) by ring,
          Real.exp_nat_mul, Real.exp_log hMpos]
        dsimp [lmb]
        rw [bernoulliMgfKL]
        ring
  have hexp :
      Tendsto (fun q : ℕ ↦ Real.exp (-(q : ℝ)))
        atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hconstMu :
      Tendsto (fun _ : ℕ ↦ μvec i) atTop (nhds (μvec i)) :=
    tendsto_const_nhds
  have hconstOneMu :
      Tendsto (fun _ : ℕ ↦ 1 - μvec i) atTop
        (nhds (1 - μvec i)) :=
    tendsto_const_nhds
  have hlim :
      Tendsto
        (fun q : ℕ ↦
          (μvec i * Real.exp (-(q : ℝ)) + (1 - μvec i)) ^ u)
        atTop (nhds ((1 - μvec i) ^ u)) := by
    simpa using ((hconstMu.mul hexp).add hconstOneMu).pow u
  rw [← bernoulli_entropy_zero_exp_KL hμ1]
  exact ge_of_tendsto' hlim hbound

/-- Adaptive stopped form of Corollary 10.4, Eq. (10.3), for the lower
Bernoulli KL tail.  The explicit interval hypotheses on the stopped average
make this lemma independent of any particular support encoding. -/
private theorem adaptive_armStoppedBernoulli_kl_lower_tail_proof
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    {π : BanditPolicy k} (i : Fin k) (u : ℕ) (hu : 0 < u)
    (hμ0 : 0 < μvec i) (hμ1 : μvec i < 1) (c : ℝ) :
    let stoppedAverage := fun h : BanditHistory k n ↦
      (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) / (u : ℝ)
    (banditMeasure ν π n).real
        {h |
          u ≤ armPullCount i h ∧
          stoppedAverage h ∈ Set.Icc (0 : ℝ) 1 ∧
          stoppedAverage h < μvec i ∧
          c < bernoulliRelativeEntropy (stoppedAverage h) (μvec i)} ≤
      Real.exp (-((u : ℝ) * c)) := by
  dsimp only
  let μhist := banditMeasure ν π n
  by_cases hc0 : c ≤ 0
  · calc
      μhist.real
          {h |
            u ≤ armPullCount i h ∧
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ) < μvec i ∧
            c < bernoulliRelativeEntropy
              ((armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ)) (μvec i)}
          ≤ 1 := measureReal_le_one
      _ ≤ Real.exp (-((u : ℝ) * c)) := by
        apply Real.one_le_exp
        exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
          (Nat.cast_nonneg u) hc0)
  · have hcpos : 0 < c := lt_of_not_ge hc0
    let d0 := bernoulliRelativeEntropy 0 (μvec i)
    by_cases hcd0 : d0 ≤ c
    · have hempty :
          {h : BanditHistory k n |
            u ≤ armPullCount i h ∧
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ) < μvec i ∧
            c < bernoulliRelativeEntropy
              ((armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                (u : ℝ)) (μvec i)} = ∅ := by
          ext h
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro hh
          let p :=
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
              (u : ℝ)
          have hanti :
              bernoulliRelativeEntropy p (μvec i) ≤
                bernoulliRelativeEntropy 0 (μvec i) :=
            bernoulliRelativeEntropy_antitone_fst
              (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
              (by simpa [p] using hh.2.1.1)
              (by simpa [p] using hh.2.2.1.le)
              ⟨hμ0, hμ1⟩
          dsimp [d0] at hcd0
          linarith
      rw [hempty, measureReal_def, measure_empty, ENNReal.toReal_zero]
      exact (Real.exp_pos _).le
    · have hclt : c < d0 := lt_of_not_ge hcd0
      have hself :
          bernoulliRelativeEntropy (μvec i) (μvec i) = 0 :=
        bernoulliRelativeEntropy_self_ast (hμ i)
      have hcMem :
          c ∈ Set.Icc
            (bernoulliRelativeEntropy (μvec i) (μvec i))
            (bernoulliRelativeEntropy 0 (μvec i)) := by
        rw [hself]
        exact ⟨hcpos.le, hclt.le⟩
      obtain ⟨r, hrIcc, hre⟩ :=
        (Set.mem_image _ _ _).mp
          (intermediate_value_Icc' (hμ i).1
            (continuous_bernoulliRelativeEntropy_fst_ast
              ⟨hμ0, hμ1⟩).continuousOn hcMem)
      have hr0 : 0 < r := by
        rcases eq_or_lt_of_le hrIcc.1 with rfl | hr
        · dsimp [d0] at hclt
          rw [hre] at hclt
          exact (lt_irrefl c hclt).elim
        · exact hr
      have hrμ : r < μvec i := by
        rcases eq_or_lt_of_le hrIcc.2 with hr | hr
        · rw [hr, hself] at hre
          linarith
        · exact hr
      have htail :=
      adaptive_armStoppedBernoulli_lower_tail_interior_KL
        (n := n) μvec hμ ν hν (π := π) i u hμ0 hμ1 hr0 hrμ
      calc
        μhist.real
            {h : BanditHistory k n |
              u ≤ armPullCount i h ∧
              (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                  (u : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
              (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                  (u : ℝ) < μvec i ∧
              c < bernoulliRelativeEntropy
                ((armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
                  (u : ℝ)) (μvec i)} ≤
            μhist.real
              {h : BanditHistory k n |
                u ≤ armPullCount i h ∧
                armStoppedCenteredSum ν i u n h +
                    μvec i * (u : ℝ) ≤ (u : ℝ) * r} := by
          apply measureReal_mono (h₂ := measure_ne_top _ _)
          intro h hh
          refine ⟨hh.1, ?_⟩
          let p :=
            (armStoppedCenteredSum ν i u n h + μvec i * (u : ℝ)) /
              (u : ℝ)
          have hpr : p < r := by
            by_contra hnot
            have hrp : r ≤ p := le_of_not_gt hnot
            have hrIcc01 : r ∈ Set.Icc (0 : ℝ) 1 :=
              ⟨hrIcc.1, le_trans hrIcc.2 (hμ i).2⟩
            have hanti :
                bernoulliRelativeEntropy p (μvec i) ≤
                  bernoulliRelativeEntropy r (μvec i) :=
              bernoulliRelativeEntropy_antitone_fst
                hrIcc01 hrp (by simpa [p] using hh.2.2.1.le)
                ⟨hμ0, hμ1⟩
            rw [hre] at hanti
            exact (not_lt_of_ge hanti) hh.2.2.2
          dsimp [p] at hpr
          have hcast : (0 : ℝ) < (u : ℝ) := Nat.cast_pos.mpr hu
          rw [div_lt_iff₀ hcast] at hpr
          nlinarith
        _ ≤ Real.exp (-((u : ℝ) *
              bernoulliRelativeEntropy r (μvec i))) := htail
        _ = Real.exp (-((u : ℝ) * c)) := by rw [hre]

end BanditAlgorithm

theorem solution
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    {π : BanditAlgorithm.BanditPolicy k} (i : Fin k)
    (u : ℕ) (hu : 0 < u)
    (hμ0 : 0 < μvec i) (hμ1 : μvec i < 1) (c : ℝ) :
    let stoppedAverage := fun h : BanditAlgorithm.BanditHistory k n ↦
      (BanditAlgorithm.armStoppedCenteredSum ν i u n h +
        μvec i * (u : ℝ)) / (u : ℝ)
    (BanditAlgorithm.banditMeasure ν π n).real
        {h |
          u ≤ BanditAlgorithm.armPullCount i h ∧
          stoppedAverage h ∈ Set.Icc (0 : ℝ) 1 ∧
          stoppedAverage h < μvec i ∧
          c < BanditAlgorithm.bernoulliRelativeEntropy
            (stoppedAverage h) (μvec i)} ≤
      Real.exp (-((u : ℝ) * c)) :=
  BanditAlgorithm.adaptive_armStoppedBernoulli_kl_lower_tail_proof
    μvec hμ ν hν i u hu hμ0 hμ1 c
