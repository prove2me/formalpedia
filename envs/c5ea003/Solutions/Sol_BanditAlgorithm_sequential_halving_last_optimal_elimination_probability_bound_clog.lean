-- Prove2me | solution 1 for BanditAlgorithm.sequential_halving_last_optimal_elimination_probability_bound_clog
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T17:58:55.432118+00:00
-- url     : https://prove2.me/submissions/b62ab250-a283-4fc5-8b4e-fae68b5873c4

import Definitions.Def_SequentialHalvingBadFinal
import Theorems.Thm_BanditAlgorithm_sequential_halving_rank_tail_average_bound_clog_min
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def windowLinearCenteredSum {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ)
    (h : BanditHistory k m) : ℝ :=
  ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi then
    θ (h r).1 * ((h r).2 - banditArmMean ν (h r).1) else 0

private noncomputable def windowQuadraticCount {k m : ℕ}
    (θ : Fin k → ℝ) (lo hi : ℕ) (h : BanditHistory k m) : ℝ :=
  ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi then θ (h r).1 ^ 2 else 0

private noncomputable def windowExpScore {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ)
    (h : BanditHistory k m) : ℝ :=
  Real.exp (windowLinearCenteredSum ν θ lo hi h -
    windowQuadraticCount θ lo hi h / 2)

private lemma windowLinearCenteredSum_snoc {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    windowLinearCenteredSum ν θ lo hi
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      windowLinearCenteredSum ν θ lo hi h +
        if lo ≤ m ∧ m < hi then θ z.1 * (z.2 - banditArmMean ν z.1) else 0 := by
  simp only [windowLinearCenteredSum, Fin.sum_univ_castSucc]
  by_cases hm : lo ≤ m ∧ m < hi <;> simp [hm]

private lemma windowQuadraticCount_snoc {k m : ℕ}
    (θ : Fin k → ℝ) (lo hi : ℕ) (h : BanditHistory k m)
    (z : Fin k × ℝ) :
    windowQuadraticCount θ lo hi
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      windowQuadraticCount θ lo hi h +
        if lo ≤ m ∧ m < hi then θ z.1 ^ 2 else 0 := by
  simp only [windowQuadraticCount, Fin.sum_univ_castSucc]
  by_cases hm : lo ≤ m ∧ m < hi <;> simp [hm]

private lemma windowExpScore_snoc {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    windowExpScore ν θ lo hi
        (Fin.snoc (α := fun _ ↦ Fin k × ℝ) h z) =
      windowExpScore ν θ lo hi h *
        Real.exp (if lo ≤ m ∧ m < hi then
          θ z.1 * (z.2 - banditArmMean ν z.1) - θ z.1 ^ 2 / 2 else 0) := by
  rw [windowExpScore, windowExpScore, windowLinearCenteredSum_snoc,
    windowQuadraticCount_snoc]
  by_cases hm : lo ≤ m ∧ m < hi
  · simp only [hm, if_pos, true_and]
    rw [← Real.exp_add]
    congr 1
    ring
  · simp [hm]

private lemma measurable_windowLinearCenteredSum {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ) :
    Measurable (windowLinearCenteredSum ν θ lo hi : BanditHistory k m → ℝ) := by
  change Measurable (fun h : BanditHistory k m ↦
    ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi then
      θ (h r).1 * ((h r).2 - banditArmMean ν (h r).1) else 0)
  apply Finset.measurable_sum
  intro r _hr
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · simp only [hrange, if_pos]
    have harm : Measurable (fun h : BanditHistory k m ↦ (h r).1) :=
      measurable_fst.comp (measurable_pi_apply r)
    have hre : Measurable (fun h : BanditHistory k m ↦ (h r).2) :=
      measurable_snd.comp (measurable_pi_apply r)
    exact ((measurable_of_countable θ).comp harm).mul
      (hre.sub ((measurable_of_countable (banditArmMean ν)).comp harm))
  · simp [hrange]

private lemma measurable_windowQuadraticCount {k m : ℕ}
    (θ : Fin k → ℝ) (lo hi : ℕ) :
    Measurable (windowQuadraticCount θ lo hi : BanditHistory k m → ℝ) := by
  change Measurable (fun h : BanditHistory k m ↦
    ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi then θ (h r).1 ^ 2 else 0)
  apply Finset.measurable_sum
  intro r _hr
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · simp only [hrange, if_pos]
    have harm : Measurable (fun h : BanditHistory k m ↦ (h r).1) :=
      measurable_fst.comp (measurable_pi_apply r)
    exact (((measurable_of_countable θ).comp harm).pow_const 2)
  · simp [hrange]

private lemma measurable_windowExpScore {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ) :
    Measurable (windowExpScore ν θ lo hi : BanditHistory k m → ℝ) := by
  exact ((measurable_windowLinearCenteredSum ν θ lo hi).sub
    ((measurable_windowQuadraticCount θ lo hi).div_const 2)).exp

private lemma measurable_windowFactor {k m : ℕ}
    (ν : StochasticBandit k) (θ : Fin k → ℝ) (lo hi : ℕ) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      Real.exp (if lo ≤ m ∧ m < hi then
        θ p.2.1 * (p.2.2 - banditArmMean ν p.2.1) - θ p.2.1 ^ 2 / 2 else 0)) := by
  by_cases hm : lo ≤ m ∧ m < hi
  · simp only [hm, if_pos]
    apply Measurable.exp
    have ha : Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ p.2.1) :=
      measurable_snd.fst
    have hx : Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦ p.2.2) :=
      measurable_snd.snd
    exact (((measurable_of_countable θ).comp ha).mul
      (hx.sub ((measurable_of_countable (banditArmMean ν)).comp ha))).sub
        ((((measurable_of_countable θ).comp ha).pow_const 2).div_const 2)
  · simp [hm]

private lemma integrable_windowFactor_kernel {k m : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (θ : Fin k → ℝ) (lo hi : ℕ) :
    Integrable (fun z : Fin k × ℝ ↦
      Real.exp (if lo ≤ m ∧ m < hi then
        θ z.1 * (z.2 - banditArmMean ν z.1) - θ z.1 ^ 2 / 2 else 0))
      (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_windowFactor ν θ lo hi).comp
      ((measurable_const : Measurable (fun _ : Fin k × ℝ ↦ h)).prodMk
        measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    by_cases hm : lo ≤ m ∧ m < hi
    · simp only [Function.comp_apply, id_eq, hm, if_pos]
      rw [show (banditRewardKernel ν) a = ν.P a by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      have hbase := (hν.2 a).integrable_exp_mul (θ a) |>.mul_const
        (Real.exp (-(θ a ^ 2 / 2)))
      convert hbase using 1
      funext y
      rw [← Real.exp_add]
      congr 1
    · simp [hm]
  · exact Integrable.of_finite

private lemma banditStepKernel_integral_windowFactor_le_one {k m : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (θ : Fin k → ℝ) (lo hi : ℕ) :
    ∫ z : Fin k × ℝ, Real.exp (if lo ≤ m ∧ m < hi then
        θ z.1 * (z.2 - banditArmMean ν z.1) - θ z.1 ^ 2 / 2 else 0)
      ∂banditStepKernel ν π m h ≤ 1 := by
  have hint := integrable_windowFactor_kernel ν hν π h θ lo hi
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp (if lo ≤ m ∧ m < hi then
        θ a * (y - banditArmMean ν a) - θ a ^ 2 / 2 else 0)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) ≤ ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      by_cases hm : lo ≤ m ∧ m < hi
      · simp only [hm, if_pos]
        rw [show (banditRewardKernel ν) a = ν.P a by
          simp [banditRewardKernel, Kernel.ofFunOfCountable]]
        have hmgf := (hν.2 a).mgf_le (θ a)
        rw [mgf] at hmgf
        have hmgf' :
            (∫ y, Real.exp (θ a * (y - banditArmMean ν a)) ∂ν.P a) ≤
              Real.exp (θ a ^ 2 / 2) := by
          simpa using hmgf
        calc
          (∫ y, Real.exp (θ a * (y - banditArmMean ν a) - θ a ^ 2 / 2)
              ∂ν.P a) = Real.exp (-(θ a ^ 2 / 2)) *
                ∫ y, Real.exp (θ a * (y - banditArmMean ν a)) ∂ν.P a := by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards with y
              rw [← Real.exp_add]
              congr 1
              ring
          _ ≤ Real.exp (-(θ a ^ 2 / 2)) * Real.exp (θ a ^ 2 / 2) :=
            mul_le_mul_of_nonneg_left hmgf' (Real.exp_nonneg _)
          _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
      · simp [hm]
    _ = 1 := by simp

private lemma integrable_compProd_windowExpScore_factor
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {m : ℕ} (μ : Measure (BanditHistory k m))
    [IsProbabilityMeasure μ] (θ : Fin k → ℝ) (lo hi : ℕ)
    (hold : Integrable
      (windowExpScore ν θ lo hi : BanditHistory k m → ℝ) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      windowExpScore ν θ lo hi p.1 *
        Real.exp (if lo ≤ m ∧ m < hi then
          θ p.2.1 * (p.2.2 - banditArmMean ν p.2.1) - θ p.2.1 ^ 2 / 2 else 0))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    windowExpScore ν θ lo hi p.1 *
      Real.exp (if lo ≤ m ∧ m < hi then
        θ p.2.1 * (p.2.2 - banditArmMean ν p.2.1) - θ p.2.1 ^ 2 / 2 else 0)
  have hG : StronglyMeasurable G :=
    (((measurable_windowExpScore ν θ lo hi).comp measurable_fst).mul
      (measurable_windowFactor ν θ lo hi)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_windowFactor_kernel ν hν π h θ lo hi).const_mul
        (windowExpScore ν θ lo hi h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ windowExpScore ν θ lo hi h := Real.exp_nonneg _
    have hcond := banditStepKernel_integral_windowFactor_le_one
      ν hν π h θ lo hi
    have hinner_nonneg : 0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖windowExpScore ν θ lo hi h *
      Real.exp (if lo ≤ m ∧ m < hi then
        θ z.1 * (z.2 - banditArmMean ν z.1) - θ z.1 ^ 2 / 2 else 0)‖
      ∂banditStepKernel ν π m h) ≤ ‖windowExpScore ν θ lo hi h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

private lemma windowExpScore_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (θ : Fin k → ℝ) (lo hi : ℕ) : ∀ m : ℕ,
    Integrable (windowExpScore ν θ lo hi : BanditHistory k m → ℝ)
      (banditMeasure ν π m) ∧
    ∫ h, windowExpScore ν θ lo hi h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;> simp [banditMeasure, windowExpScore,
        windowLinearCenteredSum, windowQuadraticCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        windowExpScore ν θ lo hi p.1 *
          Real.exp (if lo ≤ m ∧ m < hi then
            θ p.2.1 * (p.2.2 - banditArmMean ν p.2.1) - θ p.2.1 ^ 2 / 2 else 0)
      have hrewrite : (fun p ↦ windowExpScore ν θ lo hi (snoc p)) = F := by
        funext p
        exact windowExpScore_snoc ν θ lo hi p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_windowExpScore_factor ν hν μ θ lo hi ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_windowExpScore (m := m + 1) ν θ lo hi).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable (fun p ↦ windowExpScore ν θ lo hi (snoc p)) (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_windowExpScore (m := m + 1) ν θ lo hi).aestronglyMeasurable]
        change (∫ p, windowExpScore ν θ lo hi (snoc p) ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, windowExpScore ν θ lo hi h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, windowExpScore ν θ lo hi h *
              Real.exp (if lo ≤ m ∧ m < hi then
                θ z.1 * (z.2 - banditArmMean ν z.1) - θ z.1 ^ 2 / 2 else 0)
              ∂κ h) ≤ windowExpScore ν θ lo hi h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_windowFactor_le_one ν hν π h θ lo hi)
          _ ≤ 1 := ih.2

private noncomputable def windowArmMass {k m : ℕ} (i : Fin k)
    (lo hi : ℕ) (h : BanditHistory k m) : ℝ :=
  ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i then 1 else 0

private noncomputable def windowArmCenteredSum {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (lo hi : ℕ)
    (h : BanditHistory k m) : ℝ :=
  ∑ r : Fin m, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i then
    (h r).2 - banditArmMean ν i else 0

private lemma windowLinearCenteredSum_pair {k m : ℕ}
    (ν : StochasticBandit k) (i j : Fin k) (hij : i ≠ j)
    (lam : ℝ) (lo hi : ℕ) (h : BanditHistory k m) :
    windowLinearCenteredSum ν
        (fun a ↦ if a = i then lam else if a = j then -lam else 0) lo hi h =
      lam * (windowArmCenteredSum ν i lo hi h -
        windowArmCenteredSum ν j lo hi h) := by
  rw [windowLinearCenteredSum, windowArmCenteredSum, windowArmCenteredSum,
    mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · by_cases hri : (h r).1 = i
    · have hrj : (h r).1 ≠ j := by intro h; exact hij (hri.symm.trans h)
      simp [hrange, hri, hrj, hij]
    · by_cases hrj : (h r).1 = j
      · simp [hrange, hri, hrj, hij, Ne.symm hij]
      · simp [hrange, hri, hrj]
  · have hni : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i) := by
      intro hbad
      exact hrange ⟨hbad.1, hbad.2.1⟩
    have hnj : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = j) := by
      intro hbad
      exact hrange ⟨hbad.1, hbad.2.1⟩
    simp [hrange, hni, hnj]

private lemma windowQuadraticCount_pair {k m : ℕ}
    (i j : Fin k) (hij : i ≠ j) (lam : ℝ) (lo hi : ℕ)
    (h : BanditHistory k m) :
    windowQuadraticCount
        (fun a ↦ if a = i then lam else if a = j then -lam else 0) lo hi h =
      lam ^ 2 * (windowArmMass i lo hi h + windowArmMass j lo hi h) := by
  rw [windowQuadraticCount, windowArmMass, windowArmMass,
    mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · by_cases hri : (h r).1 = i
    · have hrj : (h r).1 ≠ j := by intro h; exact hij (hri.symm.trans h)
      simp [hrange, hri, hrj, hij]
    · by_cases hrj : (h r).1 = j
      · simp [hrange, hri, hrj, hij, Ne.symm hij]
      · simp [hrange, hri, hrj]
  · have hni : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i) := by
      intro hbad
      exact hrange ⟨hbad.1, hbad.2.1⟩
    have hnj : ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = j) := by
      intro hbad
      exact hrange ⟨hbad.1, hbad.2.1⟩
    simp [hrange, hni, hnj]

private theorem bandit_window_pair_centered_comparison_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (i j : Fin k) (hij : i ≠ j)
    (lo hi u : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          windowArmMass i lo hi h = (u : ℝ) ∧
          windowArmMass j lo hi h = (u : ℝ) ∧
          (u : ℝ) * delta ≤
            windowArmCenteredSum ν i lo hi h -
              windowArmCenteredSum ν j lo hi h} ≤
      Real.exp (-(u : ℝ) * delta ^ 2 / 4) := by
  let lam : ℝ := delta / 2
  let θ : Fin k → ℝ := fun a ↦ if a = i then lam else if a = j then -lam else 0
  let μ := banditMeasure ν π n
  let X : BanditHistory k n → ℝ := fun h ↦
    windowLinearCenteredSum ν θ lo hi h - windowQuadraticCount θ lo hi h / 2
  have hscore := windowExpScore_integrable_and_integral_le_one
    ν hν (π := π) θ lo hi n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp (X h)) =
      windowExpScore ν θ lo hi := by rfl
  have hint : Integrable (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h)) μ := by
    simpa [hexp] using hscore.1
  have hthreshold : 0 ≤ (u : ℝ) * delta ^ 2 / 4 := by positivity
  have hchern := measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
    ((u : ℝ) * delta ^ 2 / 4) (by positivity : (0 : ℝ) ≤ 1) hint
  calc
    μ.real {h : BanditHistory k n |
        windowArmMass i lo hi h = (u : ℝ) ∧
        windowArmMass j lo hi h = (u : ℝ) ∧
        (u : ℝ) * delta ≤ windowArmCenteredSum ν i lo hi h -
          windowArmCenteredSum ν j lo hi h} ≤
      μ.real {h | (u : ℝ) * delta ^ 2 / 4 ≤ X h} := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro h hh
        rcases hh with ⟨hmi, hmj, hcomp⟩
        dsimp [X]
        rw [windowLinearCenteredSum_pair ν i j hij lam lo hi h,
          windowQuadraticCount_pair i j hij lam lo hi h, hmi, hmj]
        dsimp [lam]
        nlinarith [mul_nonneg (Nat.cast_nonneg' u) hdelta]
    _ ≤ Real.exp (-1 * ((u : ℝ) * delta ^ 2 / 4)) * mgf X μ 1 := hchern
    _ ≤ Real.exp (-1 * ((u : ℝ) * delta ^ 2 / 4)) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf]
        simpa only [one_mul, hexp] using hscore.2
      · positivity
    _ = Real.exp (-(u : ℝ) * delta ^ 2 / 4) := by
      congr 1
      ring

private lemma windowArmMass_seqHalvingPhase {k n : ℕ} (h : BanditHistory k n)
    (ℓ : ℕ) (i : Fin k) :
    windowArmMass i (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1)) h =
      (((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card : ℝ) := by
  rw [windowArmMass]
  have hbool := Finset.sum_boole (R := ℝ)
    (fun r : Fin n ↦
      seqHalvingStart k n ℓ ≤ (r : ℕ) ∧
      (r : ℕ) < seqHalvingStart k n (ℓ + 1) ∧ (h r).1 = i)
    Finset.univ
  have hset :
      Finset.univ.filter (fun r : Fin n ↦
        seqHalvingStart k n ℓ ≤ (r : ℕ) ∧
        (r : ℕ) < seqHalvingStart k n (ℓ + 1) ∧ (h r).1 = i) =
        (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i) := by
    ext r
    simp [seqHalvingPhase, and_assoc]
  rw [hbool, hset]

private lemma windowArmCenteredSum_seqHalvingPhase {k n : ℕ}
    (ν : StochasticBandit k) (h : BanditHistory k n) (ℓ : ℕ) (i : Fin k) :
    windowArmCenteredSum ν i (seqHalvingStart k n ℓ)
        (seqHalvingStart k n (ℓ + 1)) h =
      (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2) -
        (((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card : ℝ) *
          banditArmMean ν i := by
  rw [windowArmCenteredSum]
  let S := (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)
  have hsum :
      (∑ r : Fin n, if seqHalvingStart k n ℓ ≤ (r : ℕ) ∧
          (r : ℕ) < seqHalvingStart k n (ℓ + 1) ∧ (h r).1 = i then
          (h r).2 - banditArmMean ν i else 0) =
        ∑ r ∈ S, ((h r).2 - banditArmMean ν i) := by
    rw [show S = Finset.univ.filter (fun r : Fin n ↦
        seqHalvingStart k n ℓ ≤ (r : ℕ) ∧
        (r : ℕ) < seqHalvingStart k n (ℓ + 1) ∧ (h r).1 = i) by
      ext r
      simp [S, seqHalvingPhase, and_assoc]]
    rw [Finset.sum_filter]
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]

private theorem bandit_seqHalvingPhaseMean_pair_comparison_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (i j : Fin k) (hij : i ≠ j)
    (ℓ u : ℕ) (hu : 0 < u) (hu_eq : u = seqHalvingPulls k n ℓ) (delta : ℝ)
    (hdelta : delta = banditArmMean ν j - banditArmMean ν i)
    (hdelta0 : 0 ≤ delta) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card = u ∧
          ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j)).card = u ∧
          seqHalvingPhaseMean h ℓ j ≤ seqHalvingPhaseMean h ℓ i} ≤
      Real.exp (-(u : ℝ) * delta ^ 2 / 4) := by
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans
    (bandit_window_pair_centered_comparison_tail
      ν hν i j hij (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1))
        u delta hdelta0)
  intro h hh
  rcases hh with ⟨hi, hj, hmean⟩
  constructor
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hi
  constructor
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hj
  rw [windowArmCenteredSum_seqHalvingPhase,
    windowArmCenteredSum_seqHalvingPhase, hi, hj]
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hraw :
      (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) ≤
        ∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2 := by
    change
      (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) /
          (seqHalvingPulls k n ℓ : ℝ) ≤
        (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2) /
          (seqHalvingPulls k n ℓ : ℝ) at hmean
    have hpulls : seqHalvingPulls k n ℓ = u := by
      exact hu_eq.symm
    rw [hpulls] at hmean
    exact (div_le_div_iff_of_pos_right huR).mp hmean
  rw [hdelta]
  nlinarith

private lemma seqHalving_chain_card_eq_count {k : ℕ}
    (A : ℕ → Finset (Fin k)) (L : ℕ)
    (hA0 : A 0 = Finset.univ)
    (hcard : ∀ s < L, (A (s + 1)).card = ((A s).card + 1) / 2) :
    ∀ s ≤ L, (A s).card = seqHalvingCount k s := by
  intro s hs
  induction s with
  | zero => simp [hA0, seqHalvingCount]
  | succ s ih =>
      rw [hcard s (Nat.lt_of_succ_le hs), ih (Nat.le_of_succ_le hs),
        seqHalvingCount]

private lemma lastOptimalElimination_imp_pair {k n : ℕ}
    (ν : StochasticBandit k) (h : BanditHistory k n) (ℓ : ℕ)
    (hh : IsSeqHalvingLastOptimalEliminationAt k n ν h ℓ)
    (hℓ : ℓ < Nat.clog 2 k) :
    ∃ i j : Fin k,
      0 < banditGap ν i ∧ banditGap ν j = 0 ∧ i ≠ j ∧
      ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card =
        seqHalvingPulls k n ℓ ∧
      ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j)).card =
        seqHalvingPulls k n ℓ ∧
      seqHalvingPhaseMean h ℓ j ≤ seqHalvingPhaseMean h ℓ i := by
  rcases hh with ⟨A, hA0, hrun, ⟨j, hjA, hjgap⟩, hnextGap⟩
  have hstep := hrun ℓ hℓ
  have hAcard_pos : 0 < (A ℓ).card := Finset.card_pos.mpr ⟨j, hjA⟩
  have hnext_card_pos : 0 < (A (ℓ + 1)).card := by
    rw [hstep.2.1]
    omega
  obtain ⟨i, hiA⟩ := Finset.card_pos.mp hnext_card_pos
  have higap : 0 < banditGap ν i := hnextGap i hiA
  have hjnot : j ∉ A (ℓ + 1) := by
    intro hjnext
    have := hnextGap j hjnext
    linarith
  have hjdiff : j ∈ A ℓ \ A (ℓ + 1) := by simp [hjA, hjnot]
  have hcomp := hstep.2.2.1 i hiA j hjdiff
  have hicount := hstep.2.2.2.2 i (hstep.1 hiA)
  have hjcount := hstep.2.2.2.2 j hjA
  refine ⟨i, j, higap, hjgap, ?_, hicount, hjcount, hcomp⟩
  intro hij
  subst j
  linarith

/- A history-dependent exponential score.  At round `m`, `θ m h a` may depend
on the completed prefix `h` and on the arm `a` selected for the next round, but
not on the next reward.  This is the predictable version of the fixed-vector
score above. -/
private noncomputable def predictableLinearCenteredSum {k : ℕ}
    (ν : StochasticBandit k)
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ) :
    (m : ℕ) → BanditHistory k m → ℝ
  | 0, _ => 0
  | m + 1, h =>
      predictableLinearCenteredSum ν θ m (Fin.init h) +
        θ m (Fin.init h) (h (Fin.last m)).1 *
          ((h (Fin.last m)).2 - banditArmMean ν (h (Fin.last m)).1)

private noncomputable def predictableQuadraticCount {k : ℕ}
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ) :
    (m : ℕ) → BanditHistory k m → ℝ
  | 0, _ => 0
  | m + 1, h =>
      predictableQuadraticCount θ m (Fin.init h) +
        θ m (Fin.init h) (h (Fin.last m)).1 ^ 2

private noncomputable def predictableExpScore {k : ℕ}
    (ν : StochasticBandit k)
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ)
    (m : ℕ) (h : BanditHistory k m) : ℝ :=
  Real.exp (predictableLinearCenteredSum ν θ m h -
    predictableQuadraticCount θ m h / 2)

private lemma predictableLinearCenteredSum_snoc {k m : ℕ}
    (ν : StochasticBandit k)
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    predictableLinearCenteredSum ν θ (m + 1) (Fin.snoc h z) =
      predictableLinearCenteredSum ν θ m h +
        θ m h z.1 * (z.2 - banditArmMean ν z.1) := by
  simp [predictableLinearCenteredSum]

private lemma predictableQuadraticCount_snoc {k m : ℕ}
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    predictableQuadraticCount θ (m + 1) (Fin.snoc h z) =
      predictableQuadraticCount θ m h + θ m h z.1 ^ 2 := by
  simp [predictableQuadraticCount]

private lemma predictableExpScore_snoc {k m : ℕ}
    (ν : StochasticBandit k)
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    predictableExpScore ν θ (m + 1) (Fin.snoc h z) =
      predictableExpScore ν θ m h *
        Real.exp (θ m h z.1 * (z.2 - banditArmMean ν z.1) -
          θ m h z.1 ^ 2 / 2) := by
  rw [predictableExpScore, predictableExpScore,
    predictableLinearCenteredSum_snoc, predictableQuadraticCount_snoc,
    ← Real.exp_add]
  congr 1
  ring

private lemma measurable_fin_init {k m : ℕ} :
    Measurable (Fin.init : BanditHistory k (m + 1) → BanditHistory k m) := by
  rw [measurable_pi_iff]
  intro r
  exact measurable_pi_apply (Fin.castSucc r)

private lemma measurable_predictableLinearCenteredSum {k : ℕ}
    (ν : StochasticBandit k)
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ)
    (hθ : ∀ m, Measurable (fun p : BanditHistory k m × Fin k ↦ θ m p.1 p.2)) :
    ∀ m, Measurable (predictableLinearCenteredSum ν θ m) := by
  intro m
  induction m with
  | zero => simp [predictableLinearCenteredSum]
  | succ m ih =>
      have hinit : Measurable
          (Fin.init : BanditHistory k (m + 1) → BanditHistory k m) :=
        measurable_fin_init
      have ha : Measurable
          (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).1) :=
        measurable_fst.comp (measurable_pi_apply (Fin.last m))
      have hx : Measurable
          (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).2) :=
        measurable_snd.comp (measurable_pi_apply (Fin.last m))
      rw [show predictableLinearCenteredSum ν θ (m + 1) =
          fun h ↦ predictableLinearCenteredSum ν θ m (Fin.init h) +
            θ m (Fin.init h) (h (Fin.last m)).1 *
              ((h (Fin.last m)).2 - banditArmMean ν (h (Fin.last m)).1) by
        rfl]
      exact (ih.comp hinit).add
        (((hθ m).comp (hinit.prodMk ha)).mul
          (hx.sub ((measurable_of_countable (banditArmMean ν)).comp ha)))

private lemma measurable_predictableQuadraticCount {k : ℕ}
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ)
    (hθ : ∀ m, Measurable (fun p : BanditHistory k m × Fin k ↦ θ m p.1 p.2)) :
    ∀ m, Measurable (predictableQuadraticCount θ m) := by
  intro m
  induction m with
  | zero => simp [predictableQuadraticCount]
  | succ m ih =>
      have hinit : Measurable
          (Fin.init : BanditHistory k (m + 1) → BanditHistory k m) :=
        measurable_fin_init
      have ha : Measurable
          (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).1) :=
        measurable_fst.comp (measurable_pi_apply (Fin.last m))
      rw [show predictableQuadraticCount θ (m + 1) =
          fun h ↦ predictableQuadraticCount θ m (Fin.init h) +
            θ m (Fin.init h) (h (Fin.last m)).1 ^ 2 by rfl]
      exact (ih.comp hinit).add (((hθ m).comp (hinit.prodMk ha)).pow_const 2)

private lemma measurable_predictableExpScore {k : ℕ}
    (ν : StochasticBandit k)
    (θ : (m : ℕ) → BanditHistory k m → Fin k → ℝ)
    (hθ : ∀ m, Measurable (fun p : BanditHistory k m × Fin k ↦ θ m p.1 p.2))
    (m : ℕ) : Measurable (predictableExpScore ν θ m) := by
  exact ((measurable_predictableLinearCenteredSum ν θ hθ m).sub
    ((measurable_predictableQuadraticCount θ hθ m).div_const 2)).exp

private lemma measurable_predictableFactor {k m : ℕ}
    (ν : StochasticBandit k)
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2)) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      Real.exp (θ m p.1 p.2.1 * (p.2.2 - banditArmMean ν p.2.1) -
        θ m p.1 p.2.1 ^ 2 / 2)) := by
  apply Measurable.exp
  have ha : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦ p.2.1) := measurable_snd.fst
  have hx : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦ p.2.2) := measurable_snd.snd
  have hc : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦ θ m p.1 p.2.1) :=
    (hθ m).comp (measurable_fst.prodMk ha)
  exact (hc.mul (hx.sub ((measurable_of_countable (banditArmMean ν)).comp ha))).sub
    ((hc.pow_const 2).div_const 2)

private lemma integrable_predictableFactor_kernel {k m : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2)) :
    Integrable (fun z : Fin k × ℝ ↦
      Real.exp (θ m h z.1 * (z.2 - banditArmMean ν z.1) -
        θ m h z.1 ^ 2 / 2)) (banditStepKernel ν π m h) := by
  rw [banditStepKernel]
  apply (ProbabilityTheory.integrable_compProd_iff
    ((measurable_predictableFactor ν θ hθ).comp
      ((measurable_const : Measurable (fun _ : Fin k × ℝ ↦ h)).prodMk
        measurable_id)).aestronglyMeasurable).2
  constructor
  · filter_upwards with a
    rw [Kernel.comap_apply]
    simp only [Function.comp_apply, id_eq]
    rw [show (banditRewardKernel ν) a = ν.P a by
      simp [banditRewardKernel, Kernel.ofFunOfCountable]]
    have hbase := (hν.2 a).integrable_exp_mul (θ m h a) |>.mul_const
      (Real.exp (-(θ m h a ^ 2 / 2)))
    convert hbase using 1
    funext y
    rw [← Real.exp_add]
    congr 1
  · exact Integrable.of_finite

private lemma banditStepKernel_integral_predictableFactor_le_one {k m : ℕ}
    (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (π : BanditPolicy k) (h : BanditHistory k m)
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2)) :
    ∫ z : Fin k × ℝ,
        Real.exp (θ m h z.1 * (z.2 - banditArmMean ν z.1) -
          θ m h z.1 ^ 2 / 2) ∂banditStepKernel ν π m h ≤ 1 := by
  have hint := integrable_predictableFactor_kernel ν hν π h θ hθ
  rw [banditStepKernel] at hint ⊢
  rw [ProbabilityTheory.integral_compProd hint]
  calc
    (∫ a, ∫ y, Real.exp (θ m h a * (y - banditArmMean ν a) -
        θ m h a ^ 2 / 2)
        ∂((banditRewardKernel ν).comap Prod.snd measurable_snd) (h, a)
        ∂(π.select m) h) ≤ ∫ _a, (1 : ℝ) ∂(π.select m) h := by
      apply integral_mono_ae hint.integral_compProd (integrable_const 1)
      filter_upwards with a
      rw [Kernel.comap_apply]
      simp only [Function.comp_apply, id_eq]
      rw [show (banditRewardKernel ν) a = ν.P a by
        simp [banditRewardKernel, Kernel.ofFunOfCountable]]
      have hmgf := (hν.2 a).mgf_le (θ m h a)
      rw [mgf] at hmgf
      have hmgf' :
          (∫ y, Real.exp (θ m h a * (y - banditArmMean ν a)) ∂ν.P a) ≤
            Real.exp (θ m h a ^ 2 / 2) := by simpa using hmgf
      calc
        (∫ y, Real.exp (θ m h a * (y - banditArmMean ν a) -
            θ m h a ^ 2 / 2) ∂ν.P a) =
            Real.exp (-(θ m h a ^ 2 / 2)) *
              ∫ y, Real.exp (θ m h a * (y - banditArmMean ν a)) ∂ν.P a := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with y
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-(θ m h a ^ 2 / 2)) *
            Real.exp (θ m h a ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hmgf' (Real.exp_nonneg _)
        _ = 1 := by rw [← Real.exp_add]; ring_nf; simp
    _ = 1 := by simp

private lemma integrable_compProd_predictableExpScore_factor
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} {m : ℕ} (μ : Measure (BanditHistory k m))
    [IsProbabilityMeasure μ]
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2))
    (hold : Integrable (predictableExpScore ν θ m) μ) :
    Integrable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      predictableExpScore ν θ m p.1 *
        Real.exp (θ m p.1 p.2.1 * (p.2.2 - banditArmMean ν p.2.1) -
          θ m p.1 p.2.1 ^ 2 / 2))
      (μ.compProd (banditStepKernel ν π m)) := by
  let G : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
    predictableExpScore ν θ m p.1 *
      Real.exp (θ m p.1 p.2.1 * (p.2.2 - banditArmMean ν p.2.1) -
        θ m p.1 p.2.1 ^ 2 / 2)
  have hG : StronglyMeasurable G :=
    (((measurable_predictableExpScore ν θ hθ m).comp measurable_fst).mul
      (measurable_predictableFactor ν θ hθ)).stronglyMeasurable
  rw [Measure.integrable_compProd_iff hG.aestronglyMeasurable]
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      (integrable_predictableFactor_kernel ν hν π h θ hθ).const_mul
        (predictableExpScore ν θ m h)
  · apply Integrable.mono hold
      hG.norm.integral_kernel_prod_right'.aestronglyMeasurable
    filter_upwards [] with h
    have hscore : 0 ≤ predictableExpScore ν θ m h := Real.exp_nonneg _
    have hcond := banditStepKernel_integral_predictableFactor_le_one
      ν hν π h θ hθ
    have hinner_nonneg : 0 ≤ ∫ z, ‖G (h, z)‖ ∂banditStepKernel ν π m h :=
      integral_nonneg fun _ ↦ norm_nonneg _
    rw [Real.norm_of_nonneg hinner_nonneg]
    change (∫ z, ‖predictableExpScore ν θ m h *
      Real.exp (θ m h z.1 * (z.2 - banditArmMean ν z.1) -
        θ m h z.1 ^ 2 / 2)‖ ∂banditStepKernel ν π m h) ≤
          ‖predictableExpScore ν θ m h‖
    simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hscore,
      abs_of_nonneg (Real.exp_nonneg _)]
    rw [integral_const_mul]
    exact mul_le_of_le_one_right hscore hcond

private lemma predictableExpScore_integrable_and_integral_le_one
    {k : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k}
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2)) :
    ∀ m : ℕ,
      Integrable (predictableExpScore ν θ m) (banditMeasure ν π m) ∧
      ∫ h, predictableExpScore ν θ m h ∂banditMeasure ν π m ≤ 1 := by
  intro m
  induction m with
  | zero =>
      constructor <;> simp [banditMeasure, predictableExpScore,
        predictableLinearCenteredSum, predictableQuadraticCount]
  | succ m ih =>
      let μ := banditMeasure ν π m
      let κ := banditStepKernel ν π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc p.1 p.2
      let F : BanditHistory k m × (Fin k × ℝ) → ℝ := fun p ↦
        predictableExpScore ν θ m p.1 *
          Real.exp (θ m p.1 p.2.1 * (p.2.2 - banditArmMean ν p.2.1) -
            θ m p.1 p.2.1 ^ 2 / 2)
      have hrewrite : (fun p ↦ predictableExpScore ν θ (m + 1) (snoc p)) = F := by
        funext p
        exact predictableExpScore_snoc ν θ p.1 p.2
      have hcomp : Integrable F (μ.compProd κ) :=
        integrable_compProd_predictableExpScore_factor ν hν μ θ hθ ih.1
      constructor
      · rw [banditMeasure]
        apply (integrable_map_measure
          (measurable_predictableExpScore ν θ hθ (m + 1)).aestronglyMeasurable
          measurable_banditHistorySnoc.aemeasurable).2
        change Integrable (fun p ↦ predictableExpScore ν θ (m + 1) (snoc p))
          (μ.compProd κ)
        rw [hrewrite]
        exact hcomp
      · rw [banditMeasure,
          integral_map measurable_banditHistorySnoc.aemeasurable
            (measurable_predictableExpScore ν θ hθ (m + 1)).aestronglyMeasurable]
        change (∫ p, predictableExpScore ν θ (m + 1) (snoc p)
          ∂(μ.compProd κ)) ≤ 1
        rw [hrewrite, Measure.integral_compProd hcomp]
        calc
          (∫ h, ∫ z, F (h, z) ∂κ h ∂μ) ≤
              ∫ h, predictableExpScore ν θ m h ∂μ := by
            apply integral_mono_ae hcomp.integral_compProd ih.1
            filter_upwards [] with h
            change (∫ z, predictableExpScore ν θ m h *
              Real.exp (θ m h z.1 * (z.2 - banditArmMean ν z.1) -
                θ m h z.1 ^ 2 / 2) ∂κ h) ≤ predictableExpScore ν θ m h
            rw [integral_const_mul]
            exact mul_le_of_le_one_right (Real.exp_nonneg _)
              (banditStepKernel_integral_predictableFactor_le_one ν hν π h θ hθ)
          _ ≤ 1 := ih.2

private theorem bandit_predictable_exponential_score_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k}
    (θ : (r : ℕ) → BanditHistory k r → Fin k → ℝ)
    (hθ : ∀ r, Measurable (fun p : BanditHistory k r × Fin k ↦ θ r p.1 p.2))
    (x : ℝ) (hx : 0 ≤ x) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n |
          x ≤ predictableLinearCenteredSum ν θ n h -
            predictableQuadraticCount θ n h / 2} ≤
      Real.exp (-x) := by
  let X : BanditHistory k n → ℝ := fun h ↦
    predictableLinearCenteredSum ν θ n h - predictableQuadraticCount θ n h / 2
  have hscore := predictableExpScore_integrable_and_integral_le_one
    ν hν (π := π) θ hθ n
  have hexp : (fun h : BanditHistory k n ↦ Real.exp (X h)) =
      predictableExpScore ν θ n := by rfl
  have hint : Integrable (fun h : BanditHistory k n ↦ Real.exp ((1 : ℝ) * X h))
      (banditMeasure ν π n) := by
    simpa [hexp] using hscore.1
  have hchern := measure_ge_le_exp_mul_mgf
    (μ := banditMeasure ν π n) (X := X) x (by positivity : (0 : ℝ) ≤ 1) hint
  calc
    (banditMeasure ν π n).real {h : BanditHistory k n | x ≤ X h} ≤
        Real.exp (-1 * x) * mgf X (banditMeasure ν π n) 1 := hchern
    _ ≤ Real.exp (-1 * x) * 1 := by
      apply mul_le_mul_of_nonneg_left
      · rw [mgf]
        simpa only [one_mul, hexp] using hscore.2
      · positivity
    _ = Real.exp (-x) := by ring_nf

/-- The first zero-gap arm selected at or after round `lo` in a prefix.  The
state is updated before seeing each new reward, so it is predictable. -/
private noncomputable def firstOptimalArmFrom {k : ℕ} (ν : StochasticBandit k)
    (lo hi : ℕ) : (m : ℕ) → BanditHistory k m → Fin (k + 1)
  | 0, _ => Fin.last k
  | m + 1, h =>
      if lo ≤ m ∧ m < hi then
        if firstOptimalArmFrom ν lo hi m (Fin.init h) ≠ Fin.last k then
          firstOptimalArmFrom ν lo hi m (Fin.init h)
        else if banditGap ν (h (Fin.last m)).1 = 0 then
          Fin.castSucc (h (Fin.last m)).1
        else Fin.last k
      else firstOptimalArmFrom ν lo hi m (Fin.init h)

private lemma firstOptimalArmFrom_snoc {k m : ℕ} (ν : StochasticBandit k)
    (lo hi : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    firstOptimalArmFrom ν lo hi (m + 1) (Fin.snoc h z) =
      if lo ≤ m ∧ m < hi then
        if firstOptimalArmFrom ν lo hi m h ≠ Fin.last k then
          firstOptimalArmFrom ν lo hi m h
        else if banditGap ν z.1 = 0 then Fin.castSucc z.1 else Fin.last k
      else firstOptimalArmFrom ν lo hi m h := by
  simp [firstOptimalArmFrom]

private lemma measurable_firstOptimalArmFrom {k : ℕ} (ν : StochasticBandit k)
    (lo hi : ℕ) : ∀ m, Measurable (firstOptimalArmFrom ν lo hi m) := by
  intro m
  induction m with
  | zero => simp [firstOptimalArmFrom]
  | succ m ih =>
      by_cases hm : lo ≤ m ∧ m < hi
      · let update : Fin (k + 1) × Fin k → Fin (k + 1) := fun p ↦
          if p.1 ≠ Fin.last k then p.1
          else if banditGap ν p.2 = 0 then Fin.castSucc p.2 else Fin.last k
        have hupdate : Measurable update := measurable_of_countable update
        have hinit : Measurable
            (Fin.init : BanditHistory k (m + 1) → BanditHistory k m) :=
          measurable_fin_init
        have ha : Measurable
            (fun h : BanditHistory k (m + 1) ↦ (h (Fin.last m)).1) :=
          measurable_fst.comp (measurable_pi_apply (Fin.last m))
        rw [show firstOptimalArmFrom ν lo hi (m + 1) = fun h ↦
            if lo ≤ m ∧ m < hi then
              update (firstOptimalArmFrom ν lo hi m (Fin.init h),
                (h (Fin.last m)).1)
            else firstOptimalArmFrom ν lo hi m (Fin.init h) by
          funext h
          simp [firstOptimalArmFrom, update]]
        simp only [hm, if_true]
        exact hupdate.comp ((ih.comp hinit).prodMk ha)
      · let update : Fin (k + 1) × Fin k → Fin (k + 1) := fun p ↦
          if p.1 ≠ Fin.last k then p.1
          else if banditGap ν p.2 = 0 then Fin.castSucc p.2 else Fin.last k
        have hinit : Measurable
            (Fin.init : BanditHistory k (m + 1) → BanditHistory k m) :=
          measurable_fin_init
        rw [show firstOptimalArmFrom ν lo hi (m + 1) = fun h ↦
            if lo ≤ m ∧ m < hi then
              update (firstOptimalArmFrom ν lo hi m (Fin.init h),
                (h (Fin.last m)).1)
            else firstOptimalArmFrom ν lo hi m (Fin.init h) by
          funext h
          simp [firstOptimalArmFrom, update]]
        simp only [hm, if_false]
        exact ih.comp hinit

private noncomputable def firstOptimalPairCoeff {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (lam : ℝ) (lo hi : ℕ)
    (m : ℕ) (h : BanditHistory k m) (a : Fin k) : ℝ :=
  if lo ≤ m ∧ m < hi then
    if a = i then lam
    else if firstOptimalArmFrom ν lo hi m h ≠ Fin.last k then
      if Fin.castSucc a = firstOptimalArmFrom ν lo hi m h then -lam else 0
    else if banditGap ν a = 0 then -lam else 0
  else 0

private lemma measurable_firstOptimalPairCoeff {k : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (lam : ℝ) (lo hi : ℕ) :
    ∀ m, Measurable (fun p : BanditHistory k m × Fin k ↦
      firstOptimalPairCoeff ν i lam lo hi m p.1 p.2) := by
  intro m
  by_cases hm : lo ≤ m ∧ m < hi
  · let eval : Fin (k + 1) × Fin k → ℝ := fun p ↦
      if p.2 = i then lam
      else if p.1 ≠ Fin.last k then
        if Fin.castSucc p.2 = p.1 then -lam else 0
      else if banditGap ν p.2 = 0 then -lam else 0
    have heval : Measurable eval := measurable_of_countable eval
    have href : Measurable (fun p : BanditHistory k m × Fin k ↦
        firstOptimalArmFrom ν lo hi m p.1) :=
      (measurable_firstOptimalArmFrom ν lo hi m).comp measurable_fst
    have ha : Measurable (fun p : BanditHistory k m × Fin k ↦ p.2) := measurable_snd
    simpa [firstOptimalPairCoeff, hm, eval] using heval.comp (href.prodMk ha)
  · simp [firstOptimalPairCoeff, hm]

private lemma windowArmMass_snoc {k m : ℕ} (i : Fin k) (lo hi : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    windowArmMass i lo hi (Fin.snoc h z) = windowArmMass i lo hi h +
      if lo ≤ m ∧ m < hi ∧ z.1 = i then 1 else 0 := by
  rw [windowArmMass, windowArmMass, Fin.sum_univ_castSucc]
  simp

private lemma windowArmCenteredSum_snoc {k m : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (lo hi : ℕ) (h : BanditHistory k m) (z : Fin k × ℝ) :
    windowArmCenteredSum ν i lo hi (Fin.snoc h z) =
      windowArmCenteredSum ν i lo hi h +
        if lo ≤ m ∧ m < hi ∧ z.1 = i then z.2 - banditArmMean ν i else 0 := by
  simp [windowArmCenteredSum, Fin.sum_univ_castSucc]

private lemma firstOptimalArmFrom_valid {k m : ℕ} (ν : StochasticBandit k)
    (lo hi : ℕ) (h : BanditHistory k m) :
    firstOptimalArmFrom ν lo hi m h = Fin.last k ∨
      ∃ j : Fin k, firstOptimalArmFrom ν lo hi m h = Fin.castSucc j ∧
        banditGap ν j = 0 := by
  induction m with
  | zero => simp [firstOptimalArmFrom]
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by
        simp [h', z, Fin.snoc_init_self]]
      rw [firstOptimalArmFrom_snoc]
      by_cases hrange : lo ≤ m ∧ m < hi
      · simp only [hrange, if_true]
        rcases ih h' with hs | ⟨j, hjcode, hjgap⟩
        · rw [hs]
          simp only [ne_eq, not_true_eq_false, if_false]
          by_cases hz : banditGap ν z.1 = 0
          · exact Or.inr ⟨z.1, by simp [hz], hz⟩
          · exact Or.inl (by simp [hz])
        · have hne : firstOptimalArmFrom ν lo hi m h' ≠ Fin.last k := by
            rw [hjcode]
            exact Fin.castSucc_ne_last j
          rw [if_pos hne]
          exact Or.inr ⟨j, hjcode, hjgap⟩
      · simp only [hrange, if_false]
        exact ih h'

private noncomputable def firstOptimalReferenceIndicator {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m)
    (a : Fin k) : ℝ :=
  if lo ≤ m ∧ m < hi then
    if firstOptimalArmFrom ν lo hi m h ≠ Fin.last k then
      if Fin.castSucc a = firstOptimalArmFrom ν lo hi m h then 1 else 0
    else if banditGap ν a = 0 then 1 else 0
  else 0

private lemma firstOptimalReferenceIndicator_for_suboptimal {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (hiGap : banditGap ν i ≠ 0)
    (lo hi : ℕ) (h : BanditHistory k m) :
    firstOptimalReferenceIndicator ν lo hi h i = 0 := by
  rw [firstOptimalReferenceIndicator]
  by_cases hrange : lo ≤ m ∧ m < hi
  · simp only [hrange, if_true]
    rcases firstOptimalArmFrom_valid ν lo hi h with hs | ⟨j, hjcode, hjgap⟩
    · simp [hs, hiGap]
    · have hne : firstOptimalArmFrom ν lo hi m h ≠ Fin.last k := by
        rw [hjcode]
        exact Fin.castSucc_ne_last j
      rw [if_pos hne]
      by_cases hij : Fin.castSucc i = firstOptimalArmFrom ν lo hi m h
      · rw [hjcode] at hij
        have : i = j := by
          apply Fin.ext
          exact congrArg (fun x : Fin (k + 1) ↦ x.val) hij
        subst j
        exact (hiGap hjgap).elim
      · rw [if_neg hij]
        simp
  · simp [hrange]

private lemma firstOptimalPairCoeff_eq_indicator {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (hiGap : banditGap ν i ≠ 0)
    (lam : ℝ) (lo hi : ℕ) (h : BanditHistory k m) (a : Fin k) :
    firstOptimalPairCoeff ν i lam lo hi m h a =
      lam * ((if lo ≤ m ∧ m < hi ∧ a = i then 1 else 0) -
        firstOptimalReferenceIndicator ν lo hi h a) := by
  by_cases hrange : lo ≤ m ∧ m < hi
  · by_cases hai : a = i
    · subst a
      rw [firstOptimalReferenceIndicator_for_suboptimal ν i hiGap]
      simp [firstOptimalPairCoeff, hrange]
    · simp only [firstOptimalPairCoeff, firstOptimalReferenceIndicator,
        hrange, if_true, hai, if_false]
      by_cases hs : firstOptimalArmFrom ν lo hi m h ≠ Fin.last k
      · by_cases href : Fin.castSucc a = firstOptimalArmFrom ν lo hi m h
        · simp [hs, href]
        · simp [hs, href]
      · by_cases hgap : banditGap ν a = 0
        · simp [hs, hgap]
        · simp [hs, hgap]
  · have htriple : ¬(lo ≤ m ∧ m < hi ∧ a = i) := fun h ↦
      hrange ⟨h.1, h.2.1⟩
    simp [firstOptimalPairCoeff, firstOptimalReferenceIndicator, hrange, htriple]

private lemma firstOptimalPairCoeff_sq_eq_indicator {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (hiGap : banditGap ν i ≠ 0)
    (lam : ℝ) (lo hi : ℕ) (h : BanditHistory k m) (a : Fin k) :
    firstOptimalPairCoeff ν i lam lo hi m h a ^ 2 =
      lam ^ 2 * ((if lo ≤ m ∧ m < hi ∧ a = i then 1 else 0) +
        firstOptimalReferenceIndicator ν lo hi h a) := by
  rw [firstOptimalPairCoeff_eq_indicator ν i hiGap]
  have href0or1 : firstOptimalReferenceIndicator ν lo hi h a = 0 ∨
      firstOptimalReferenceIndicator ν lo hi h a = 1 := by
    unfold firstOptimalReferenceIndicator
    split_ifs <;> simp
  by_cases hai : a = i
  · subst a
    rw [firstOptimalReferenceIndicator_for_suboptimal ν i hiGap]
    by_cases hrange : lo ≤ m ∧ m < hi <;> simp [hrange]
  · have hnot : ¬(lo ≤ m ∧ m < hi ∧ a = i) := by simp [hai]
    simp only [hnot, if_false, zero_sub, zero_add]
    rcases href0or1 with href | href <;> rw [href] <;> ring

private noncomputable def predictableReferenceCenteredSum {k : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) :
    (m : ℕ) → BanditHistory k m → ℝ
  | 0, _ => 0
  | m + 1, h =>
      predictableReferenceCenteredSum ν lo hi m (Fin.init h) +
        firstOptimalReferenceIndicator ν lo hi (Fin.init h)
            (h (Fin.last m)).1 *
          ((h (Fin.last m)).2 - banditArmMean ν (h (Fin.last m)).1)

private noncomputable def predictableReferenceMass {k : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) :
    (m : ℕ) → BanditHistory k m → ℝ
  | 0, _ => 0
  | m + 1, h =>
      predictableReferenceMass ν lo hi m (Fin.init h) +
        firstOptimalReferenceIndicator ν lo hi (Fin.init h) (h (Fin.last m)).1

private lemma predictableReferenceCenteredSum_snoc {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    predictableReferenceCenteredSum ν lo hi (m + 1) (Fin.snoc h z) =
      predictableReferenceCenteredSum ν lo hi m h +
        firstOptimalReferenceIndicator ν lo hi h z.1 *
          (z.2 - banditArmMean ν z.1) := by
  simp [predictableReferenceCenteredSum]

private lemma predictableReferenceMass_snoc {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ)
    (h : BanditHistory k m) (z : Fin k × ℝ) :
    predictableReferenceMass ν lo hi (m + 1) (Fin.snoc h z) =
      predictableReferenceMass ν lo hi m h +
        firstOptimalReferenceIndicator ν lo hi h z.1 := by
  simp [predictableReferenceMass]

private lemma predictableLinearCenteredSum_firstOptimalPair {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (hiGap : banditGap ν i ≠ 0)
    (lam : ℝ) (lo hi : ℕ) (h : BanditHistory k m) :
    predictableLinearCenteredSum ν
        (firstOptimalPairCoeff ν i lam lo hi) m h =
      lam * (windowArmCenteredSum ν i lo hi h -
        predictableReferenceCenteredSum ν lo hi m h) := by
  induction m with
  | zero => simp [predictableLinearCenteredSum, windowArmCenteredSum,
      predictableReferenceCenteredSum]
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by simp [h', z, Fin.snoc_init_self]]
      rw [predictableLinearCenteredSum_snoc, windowArmCenteredSum_snoc,
        predictableReferenceCenteredSum_snoc, ih h',
        firstOptimalPairCoeff_eq_indicator ν i hiGap]
      by_cases hmi : lo ≤ m ∧ m < hi ∧ z.1 = i
      · have hrange : lo ≤ m ∧ m < hi := ⟨hmi.1, hmi.2.1⟩
        have hzi : z.1 = i := hmi.2.2
        simp [hrange, hzi,
          firstOptimalReferenceIndicator_for_suboptimal ν i hiGap]
        ring
      · simp only [hmi, if_false]
        ring

private lemma predictableQuadraticCount_firstOptimalPair {k m : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (hiGap : banditGap ν i ≠ 0)
    (lam : ℝ) (lo hi : ℕ) (h : BanditHistory k m) :
    predictableQuadraticCount (firstOptimalPairCoeff ν i lam lo hi) m h =
      lam ^ 2 * (windowArmMass i lo hi h +
        predictableReferenceMass ν lo hi m h) := by
  induction m with
  | zero => simp [predictableQuadraticCount, windowArmMass,
      predictableReferenceMass]
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by simp [h', z, Fin.snoc_init_self]]
      rw [predictableQuadraticCount_snoc, windowArmMass_snoc,
        predictableReferenceMass_snoc, ih h',
        firstOptimalPairCoeff_sq_eq_indicator ν i hiGap]
      by_cases hmi : lo ≤ m ∧ m < hi ∧ z.1 = i
      · simp only [hmi, if_true]
        ring
      · simp only [hmi, if_false]
        ring

private lemma firstOptimalArmFrom_eq_last_imp_window_zero {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m)
    (j : Fin k) (hjgap : banditGap ν j = 0)
    (hstate : firstOptimalArmFrom ν lo hi m h = Fin.last k) :
    windowArmMass j lo hi h = 0 ∧ windowArmCenteredSum ν j lo hi h = 0 ∧
      predictableReferenceMass ν lo hi m h = 0 ∧
      predictableReferenceCenteredSum ν lo hi m h = 0 := by
  induction m with
  | zero => simp [windowArmMass, windowArmCenteredSum,
      predictableReferenceMass, predictableReferenceCenteredSum]
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by simp [h', z, Fin.snoc_init_self]] at hstate ⊢
      rw [firstOptimalArmFrom_snoc] at hstate
      rw [windowArmMass_snoc, windowArmCenteredSum_snoc,
        predictableReferenceMass_snoc, predictableReferenceCenteredSum_snoc]
      by_cases hrange : lo ≤ m ∧ m < hi
      · simp only [hrange, if_true] at hstate
        have hprev : firstOptimalArmFrom ν lo hi m h' = Fin.last k := by
          by_contra hne
          rw [if_pos hne] at hstate
          exact hne hstate
        rw [hprev] at hstate
        simp only [ne_eq, not_true_eq_false, if_false] at hstate
        have hzgap : banditGap ν z.1 ≠ 0 := by
          intro hz
          rw [hz, if_pos rfl] at hstate
          exact Fin.castSucc_ne_last z.1 hstate
        have hzj : z.1 ≠ j := by
          intro hzj
          subst j
          exact hzgap hjgap
        rcases ih h' hprev with ⟨hmass, hsum, hrefmass, hrefsum⟩
        simp [firstOptimalReferenceIndicator, hrange, hprev, hzgap, hzj,
          hmass, hsum, hrefmass, hrefsum]
      · simp only [hrange, if_false] at hstate
        rcases ih h' hstate with ⟨hmass, hsum, hrefmass, hrefsum⟩
        have hnotj : ¬(lo ≤ m ∧ m < hi ∧ z.1 = j) := fun hz ↦
          hrange ⟨hz.1, hz.2.1⟩
        simp [firstOptimalReferenceIndicator, hrange, hnotj, hmass, hsum,
          hrefmass, hrefsum]

private lemma firstOptimalReference_eq_window {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m)
    (j : Fin k)
    (hstate : firstOptimalArmFrom ν lo hi m h = Fin.castSucc j) :
    predictableReferenceMass ν lo hi m h = windowArmMass j lo hi h ∧
      predictableReferenceCenteredSum ν lo hi m h =
        windowArmCenteredSum ν j lo hi h := by
  induction m with
  | zero =>
      exact (Fin.castSucc_ne_last j hstate.symm).elim
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by simp [h', z, Fin.snoc_init_self]] at hstate ⊢
      rw [firstOptimalArmFrom_snoc] at hstate
      rw [predictableReferenceMass_snoc, predictableReferenceCenteredSum_snoc,
        windowArmMass_snoc, windowArmCenteredSum_snoc]
      by_cases hrange : lo ≤ m ∧ m < hi
      · simp only [hrange, if_true] at hstate
        rcases firstOptimalArmFrom_valid ν lo hi h' with hs | ⟨q, hqcode, hqgap⟩
        · rw [hs] at hstate
          simp only [ne_eq, not_true_eq_false, if_false] at hstate
          have hzgap : banditGap ν z.1 = 0 := by
            by_contra hz
            rw [if_neg hz] at hstate
            exact Fin.castSucc_ne_last j hstate.symm
          rw [if_pos hzgap] at hstate
          have hzj : z.1 = j := by
            apply Fin.ext
            exact congrArg (fun x : Fin (k + 1) ↦ x.val) hstate
          have hjgap : banditGap ν j = 0 := by simpa [hzj] using hzgap
          have hzero := firstOptimalArmFrom_eq_last_imp_window_zero
            ν lo hi h' j hjgap hs
          simp [firstOptimalReferenceIndicator, hrange, hs, hzgap, hzj, hjgap,
            hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2]
        · have hqne : firstOptimalArmFrom ν lo hi m h' ≠ Fin.last k := by
            rw [hqcode]
            exact Fin.castSucc_ne_last q
          rw [if_pos hqne] at hstate
          have hqj : q = j := by
            rw [hqcode] at hstate
            apply Fin.ext
            exact congrArg (fun x : Fin (k + 1) ↦ x.val) hstate
          subst q
          rcases ih h' hqcode with ⟨hmass, hsum⟩
          by_cases hzj : z.1 = j
          · simp [firstOptimalReferenceIndicator, hrange, hqne, hqcode, hzj,
              hmass, hsum]
          · have hzcode : Fin.castSucc z.1 ≠ Fin.castSucc j := by
              intro hz
              apply hzj
              apply Fin.ext
              exact congrArg (fun x : Fin (k + 1) ↦ x.val) hz
            simp [firstOptimalReferenceIndicator, hrange, hqne, hqcode, hzj,
              hzcode, hmass, hsum]
      · simp only [hrange, if_false] at hstate
        rcases ih h' hstate with ⟨hmass, hsum⟩
        have hnotj : ¬(lo ≤ m ∧ m < hi ∧ z.1 = j) := fun hz ↦
          hrange ⟨hz.1, hz.2.1⟩
        simp [firstOptimalReferenceIndicator, hrange, hnotj, hmass, hsum]

private theorem bandit_window_first_optimal_reference_comparison_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (i : Fin k) (hiGap : 0 < banditGap ν i)
    (lo hi u : ℕ) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n | ∃ j : Fin k,
          firstOptimalArmFrom ν lo hi n h = Fin.castSucc j ∧
          windowArmMass i lo hi h = (u : ℝ) ∧
          windowArmMass j lo hi h = (u : ℝ) ∧
          (u : ℝ) * banditGap ν i ≤
            windowArmCenteredSum ν i lo hi h -
              windowArmCenteredSum ν j lo hi h} ≤
      Real.exp (-(u : ℝ) * banditGap ν i ^ 2 / 4) := by
  let lam : ℝ := banditGap ν i / 2
  let θ := firstOptimalPairCoeff ν i lam lo hi
  let x : ℝ := (u : ℝ) * banditGap ν i ^ 2 / 4
  have hx : 0 ≤ x := by positivity
  have hxeq : -(u : ℝ) * banditGap ν i ^ 2 / 4 = -x := by
    dsimp [x]
    ring
  rw [hxeq]
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans
    (bandit_predictable_exponential_score_tail ν hν θ
      (measurable_firstOptimalPairCoeff ν i lam lo hi) x hx)
  intro h hh
  rcases hh with ⟨j, hjstate, hmi, hmj, hcomp⟩
  have href := firstOptimalReference_eq_window ν lo hi h j hjstate
  change x ≤ predictableLinearCenteredSum ν θ n h -
    predictableQuadraticCount θ n h / 2
  rw [predictableLinearCenteredSum_firstOptimalPair ν i (ne_of_gt hiGap),
    predictableQuadraticCount_firstOptimalPair ν i (ne_of_gt hiGap),
    href.1, href.2, hmi, hmj]
  dsimp [x, θ, lam]
  nlinarith [mul_nonneg (Nat.cast_nonneg' u) (le_of_lt hiGap)]

private lemma firstOptimalReferenceIndicator_nonneg {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m) (a : Fin k) :
    0 ≤ firstOptimalReferenceIndicator ν lo hi h a := by
  unfold firstOptimalReferenceIndicator
  split_ifs <;> positivity

private lemma predictableReferenceMass_nonneg {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m) :
    0 ≤ predictableReferenceMass ν lo hi m h := by
  induction m with
  | zero => simp [predictableReferenceMass]
  | succ m ih =>
      rw [show h = Fin.snoc (Fin.init h) (h (Fin.last m)) by
        simp [Fin.snoc_init_self], predictableReferenceMass_snoc]
      exact add_nonneg (ih (Fin.init h))
        (firstOptimalReferenceIndicator_nonneg ν lo hi (Fin.init h) _)

private lemma firstOptimalArmFrom_selected_referenceMass_pos {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m)
    (j : Fin k) (hstate : firstOptimalArmFrom ν lo hi m h = Fin.castSucc j) :
    0 < predictableReferenceMass ν lo hi m h := by
  induction m with
  | zero => exact (Fin.castSucc_ne_last j hstate.symm).elim
  | succ m ih =>
      let h' := Fin.init h
      let z := h (Fin.last m)
      rw [show h = Fin.snoc h' z by simp [h', z, Fin.snoc_init_self]] at hstate ⊢
      rw [firstOptimalArmFrom_snoc] at hstate
      rw [predictableReferenceMass_snoc]
      by_cases hrange : lo ≤ m ∧ m < hi
      · simp only [hrange, if_true] at hstate
        rcases firstOptimalArmFrom_valid ν lo hi h' with hs | ⟨q, hqcode, hqgap⟩
        · rw [hs] at hstate
          simp only [ne_eq, not_true_eq_false, if_false] at hstate
          have hzgap : banditGap ν z.1 = 0 := by
            by_contra hz
            rw [if_neg hz] at hstate
            exact Fin.castSucc_ne_last j hstate.symm
          rw [if_pos hzgap] at hstate
          have hzj : z.1 = j := by
            apply Fin.ext
            exact congrArg (fun x : Fin (k + 1) ↦ x.val) hstate
          have hjgap : banditGap ν j = 0 := by simpa [hzj] using hzgap
          have hzero := firstOptimalArmFrom_eq_last_imp_window_zero
            ν lo hi h' j hjgap hs
          simp [firstOptimalReferenceIndicator, hrange, hs, hzgap, hzj, hjgap,
            hzero.2.2.1]
        · have hqne : firstOptimalArmFrom ν lo hi m h' ≠ Fin.last k := by
            rw [hqcode]
            exact Fin.castSucc_ne_last q
          rw [if_pos hqne] at hstate
          have hqj : q = j := by
            rw [hqcode] at hstate
            apply Fin.ext
            exact congrArg (fun x : Fin (k + 1) ↦ x.val) hstate
          subst q
          have hpos := ih h' hqcode
          exact lt_of_lt_of_le hpos (le_add_of_nonneg_right
            (firstOptimalReferenceIndicator_nonneg ν lo hi h' z.1))
      · simp only [hrange, if_false] at hstate
        have hpos := ih h' hstate
        exact lt_of_lt_of_le hpos (le_add_of_nonneg_right
          (firstOptimalReferenceIndicator_nonneg ν lo hi h' z.1))

private lemma firstOptimalArmFrom_selected_mass_pos {k m : ℕ}
    (ν : StochasticBandit k) (lo hi : ℕ) (h : BanditHistory k m)
    (j : Fin k) (hstate : firstOptimalArmFrom ν lo hi m h = Fin.castSucc j) :
    0 < windowArmMass j lo hi h := by
  have hpos := firstOptimalArmFrom_selected_referenceMass_pos
    ν lo hi h j hstate
  rw [(firstOptimalReference_eq_window ν lo hi h j hstate).1] at hpos
  exact hpos

private theorem bandit_seqHalvingPhaseMean_firstOptimal_comparison_tail
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (i : Fin k) (hiGap : 0 < banditGap ν i)
    (ℓ u : ℕ) (hu : 0 < u) (hu_eq : u = seqHalvingPulls k n ℓ) :
    (banditMeasure ν π n).real
        {h : BanditHistory k n | ∃ j : Fin k,
          firstOptimalArmFrom ν (seqHalvingStart k n ℓ)
              (seqHalvingStart k n (ℓ + 1)) n h = Fin.castSucc j ∧
          ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card = u ∧
          ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j)).card = u ∧
          seqHalvingPhaseMean h ℓ j ≤ seqHalvingPhaseMean h ℓ i} ≤
      Real.exp (-(u : ℝ) * banditGap ν i ^ 2 / 4) := by
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans
    (bandit_window_first_optimal_reference_comparison_tail
      ν hν i hiGap (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1)) u)
  intro h hh
  rcases hh with ⟨j, hjstate, hicount, hjcount, hmean⟩
  refine ⟨j, hjstate, ?_, ?_, ?_⟩
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hicount
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hjcount
  · have hjgap : banditGap ν j = 0 := by
      rcases firstOptimalArmFrom_valid ν (seqHalvingStart k n ℓ)
        (seqHalvingStart k n (ℓ + 1)) h with hs | ⟨q, hqstate, hqgap⟩
      · exact (Fin.castSucc_ne_last j (hjstate.symm.trans hs)).elim
      · have hqj : q = j := by
          have hcode : Fin.castSucc q = Fin.castSucc j := hqstate.symm.trans hjstate
          apply Fin.ext
          exact congrArg (fun x : Fin (k + 1) ↦ x.val) hcode
        simpa [hqj] using hqgap
    rw [windowArmCenteredSum_seqHalvingPhase,
      windowArmCenteredSum_seqHalvingPhase, hicount, hjcount]
    have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
    have hraw :
        (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) ≤
          ∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2 := by
      change
        (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) /
            (seqHalvingPulls k n ℓ : ℝ) ≤
          (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2) /
            (seqHalvingPulls k n ℓ : ℝ) at hmean
      rw [← hu_eq] at hmean
      exact (div_le_div_iff_of_pos_right huR).mp hmean
    have hgapmean : banditGap ν i = banditArmMean ν j - banditArmMean ν i := by
      rw [banditGap] at hjgap ⊢
      linarith
    rw [hgapmean]
    nlinarith

private lemma seqHalvingCount_le (k s : ℕ) : seqHalvingCount k s ≤ k := by
  induction s with
  | zero => simp [seqHalvingCount]
  | succ s ih =>
      rw [seqHalvingCount]
      omega

private lemma seqHalvingCount_pos (k s : ℕ) (hk : 0 < k) :
    0 < seqHalvingCount k s := by
  induction s with
  | zero => simpa [seqHalvingCount]
  | succ s ih =>
      rw [seqHalvingCount]
      exact Nat.div_pos (by omega) (by omega)

private lemma seqHalvingPulls_pos_of_budget {k n ℓ : ℕ}
    (hn : k * Nat.clog 2 k ≤ n) (hℓ : ℓ < Nat.clog 2 k) :
    0 < seqHalvingPulls k n ℓ := by
  have hL : 0 < Nat.clog 2 k := Nat.zero_lt_of_lt hℓ
  have hk : 0 < k := by
    have hp := Nat.pow_lt_of_lt_clog hℓ
    have hp0 : 0 < 2 ^ ℓ := pow_pos (by decide) _
    omega
  have hc : 0 < seqHalvingCount k ℓ := seqHalvingCount_pos k ℓ hk
  have hdenpos : 0 < Nat.clog 2 k * seqHalvingCount k ℓ :=
    Nat.mul_pos hL hc
  have hdenle : Nat.clog 2 k * seqHalvingCount k ℓ ≤ n := by
    calc
      Nat.clog 2 k * seqHalvingCount k ℓ ≤ Nat.clog 2 k * k :=
        Nat.mul_le_mul_left _ (seqHalvingCount_le k ℓ)
      _ = k * Nat.clog 2 k := Nat.mul_comm _ _
      _ ≤ n := hn
  exact Nat.div_pos hdenle hdenpos

private def IsLastOptimalEliminationWithSurvivor (k n : ℕ)
    (ν : StochasticBandit k) (h : BanditHistory k n) (ℓ : ℕ) (i : Fin k) : Prop :=
  ∃ A : ℕ → Finset (Fin k),
    A 0 = Finset.univ ∧
    (∀ s < Nat.clog 2 k,
      A (s + 1) ⊆ A s ∧
      (A (s + 1)).card = ((A s).card + 1) / 2 ∧
      (∀ a ∈ A (s + 1), ∀ b ∈ A s \ A (s + 1),
        seqHalvingPhaseMean h s b ≤ seqHalvingPhaseMean h s a) ∧
      (∀ t ∈ seqHalvingPhase k n s, (h t).1 ∈ A s) ∧
      (∀ a ∈ A s,
        ((seqHalvingPhase k n s).filter (fun t ↦ (h t).1 = a)).card =
          seqHalvingPulls k n s)) ∧
    (∃ a ∈ A ℓ, banditGap ν a = 0) ∧
    (∀ a ∈ A (ℓ + 1), 0 < banditGap ν a) ∧
    i ∈ A (ℓ + 1)

private lemma lastOptimalEliminationWithSurvivor_imp_firstOptimalEvent
    {k n : ℕ} (ν : StochasticBandit k) (hn : k * Nat.clog 2 k ≤ n)
    (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) (i : Fin k) (h : BanditHistory k n)
    (hh : IsLastOptimalEliminationWithSurvivor k n ν h ℓ i) :
    ∃ j : Fin k,
      firstOptimalArmFrom ν (seqHalvingStart k n ℓ)
          (seqHalvingStart k n (ℓ + 1)) n h = Fin.castSucc j ∧
      ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i)).card =
        seqHalvingPulls k n ℓ ∧
      ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j)).card =
        seqHalvingPulls k n ℓ ∧
      seqHalvingPhaseMean h ℓ j ≤ seqHalvingPhaseMean h ℓ i := by
  rcases hh with ⟨A, hA0, hrun, ⟨p, hpA, hpgap⟩, hnextGap, hiA⟩
  have hstep := hrun ℓ hℓ
  have hu : 0 < seqHalvingPulls k n ℓ := seqHalvingPulls_pos_of_budget hn hℓ
  have hpcount := hstep.2.2.2.2 p hpA
  have hpmass :
      windowArmMass p (seqHalvingStart k n ℓ)
          (seqHalvingStart k n (ℓ + 1)) h = (seqHalvingPulls k n ℓ : ℝ) := by
    rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hpcount
  have hstate_ne :
      firstOptimalArmFrom ν (seqHalvingStart k n ℓ)
          (seqHalvingStart k n (ℓ + 1)) n h ≠ Fin.last k := by
    intro hs
    have hzero := firstOptimalArmFrom_eq_last_imp_window_zero ν
      (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1)) h p hpgap hs
    rw [hpmass] at hzero
    have huR : (0 : ℝ) < (seqHalvingPulls k n ℓ : ℝ) := by exact_mod_cast hu
    linarith [hzero.1]
  rcases firstOptimalArmFrom_valid ν (seqHalvingStart k n ℓ)
      (seqHalvingStart k n (ℓ + 1)) h with hs | ⟨j, hjstate, hjgap⟩
  · exact (hstate_ne hs).elim
  · have hjmass_pos := firstOptimalArmFrom_selected_mass_pos ν
      (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1)) h j hjstate
    rw [windowArmMass_seqHalvingPhase] at hjmass_pos
    have hjfilter_pos :
        0 < ((seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j)).card := by
      exact_mod_cast hjmass_pos
    have hjfilter_nonempty := Finset.card_pos.mp hjfilter_pos
    rcases hjfilter_nonempty with ⟨t, ht⟩
    have htmem : t ∈ seqHalvingPhase k n ℓ := (Finset.mem_filter.mp ht).1
    have htj : (h t).1 = j := (Finset.mem_filter.mp ht).2
    have hjA : j ∈ A ℓ := by
      have := hstep.2.2.2.1 t htmem
      simpa [htj] using this
    have hjnot : j ∉ A (ℓ + 1) := by
      intro hjnext
      have := hnextGap j hjnext
      linarith
    have hjdiff : j ∈ A ℓ \ A (ℓ + 1) := by simp [hjA, hjnot]
    have hicount := hstep.2.2.2.2 i (hstep.1 hiA)
    have hjcount := hstep.2.2.2.2 j hjA
    have hcomp := hstep.2.2.1 i hiA j hjdiff
    exact ⟨j, hjstate, hicount, hjcount, hcomp⟩

private lemma measurable_windowArmMass {k n : ℕ} (i : Fin k) (lo hi : ℕ) :
    Measurable (windowArmMass i lo hi : BanditHistory k n → ℝ) := by
  rw [show (windowArmMass i lo hi : BanditHistory k n → ℝ) = fun h ↦
      ∑ r : Fin n, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i then 1 else 0 by
    rfl]
  apply Finset.measurable_sum
  intro r _hr
  have ha : Measurable (fun h : BanditHistory k n ↦ (h r).1) :=
    measurable_fst.comp (measurable_pi_apply r)
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · simp only [hrange, true_and]
    exact Measurable.ite (ha (measurableSet_singleton i))
      measurable_const measurable_const
  · have hcond (h : BanditHistory k n) :
        ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i) := fun hh ↦
      hrange ⟨hh.1, hh.2.1⟩
    simp only [if_neg (hcond _)]
    exact measurable_const

private lemma measurable_windowArmCenteredSum {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (lo hi : ℕ) :
    Measurable (windowArmCenteredSum ν i lo hi : BanditHistory k n → ℝ) := by
  rw [show (windowArmCenteredSum ν i lo hi : BanditHistory k n → ℝ) = fun h ↦
      ∑ r : Fin n, if lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i then
        (h r).2 - banditArmMean ν i else 0 by rfl]
  apply Finset.measurable_sum
  intro r _hr
  have ha : Measurable (fun h : BanditHistory k n ↦ (h r).1) :=
    measurable_fst.comp (measurable_pi_apply r)
  have hx : Measurable (fun h : BanditHistory k n ↦ (h r).2) :=
    measurable_snd.comp (measurable_pi_apply r)
  by_cases hrange : lo ≤ (r : ℕ) ∧ (r : ℕ) < hi
  · simp only [hrange, true_and]
    exact Measurable.ite (ha (measurableSet_singleton i))
      (hx.sub measurable_const) measurable_const
  · have hcond (h : BanditHistory k n) :
        ¬(lo ≤ (r : ℕ) ∧ (r : ℕ) < hi ∧ (h r).1 = i) := fun hh ↦
      hrange ⟨hh.1, hh.2.1⟩
    simp only [if_neg (hcond _)]
    exact measurable_const

private def firstOptimalComparisonEvent {k n : ℕ} (ν : StochasticBandit k)
    (i : Fin k) (lo hi u : ℕ) : Set (BanditHistory k n) :=
  ⋃ j : Fin k,
    {h | firstOptimalArmFrom ν lo hi n h = Fin.castSucc j} ∩
    {h | windowArmMass i lo hi h = (u : ℝ)} ∩
    {h | windowArmMass j lo hi h = (u : ℝ)} ∩
    {h | (u : ℝ) * banditGap ν i ≤
      windowArmCenteredSum ν i lo hi h - windowArmCenteredSum ν j lo hi h}

private lemma measurableSet_firstOptimalComparisonEvent {k n : ℕ}
    (ν : StochasticBandit k) (i : Fin k) (lo hi u : ℕ) :
    MeasurableSet (firstOptimalComparisonEvent (n := n) ν i lo hi u) := by
  apply MeasurableSet.iUnion
  intro j
  have hstate : MeasurableSet
      {h : BanditHistory k n | firstOptimalArmFrom ν lo hi n h = Fin.castSucc j} := by
    exact measurable_firstOptimalArmFrom ν lo hi n (measurableSet_singleton _)
  have hmi : MeasurableSet
      {h : BanditHistory k n | windowArmMass i lo hi h = (u : ℝ)} := by
    exact measurable_windowArmMass i lo hi (measurableSet_singleton _)
  have hmj : MeasurableSet
      {h : BanditHistory k n | windowArmMass j lo hi h = (u : ℝ)} := by
    exact measurable_windowArmMass j lo hi (measurableSet_singleton _)
  have hcomp : MeasurableSet
      {h : BanditHistory k n | (u : ℝ) * banditGap ν i ≤
        windowArmCenteredSum ν i lo hi h - windowArmCenteredSum ν j lo hi h} :=
    measurableSet_le measurable_const
      ((measurable_windowArmCenteredSum ν i lo hi).sub
        (measurable_windowArmCenteredSum ν j lo hi))
  exact ((hstate.inter hmi).inter hmj).inter hcomp

private theorem bandit_firstOptimalComparisonEvent_probability_bound
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (i : Fin k) (hiGap : 0 < banditGap ν i)
    (lo hi u : ℕ) :
    (banditMeasure ν π n).real
        (firstOptimalComparisonEvent (n := n) ν i lo hi u) ≤
      Real.exp (-(u : ℝ) * banditGap ν i ^ 2 / 4) := by
  have hset : firstOptimalComparisonEvent (n := n) ν i lo hi u =
      {h : BanditHistory k n | ∃ j : Fin k,
        firstOptimalArmFrom ν lo hi n h = Fin.castSucc j ∧
        windowArmMass i lo hi h = (u : ℝ) ∧
        windowArmMass j lo hi h = (u : ℝ) ∧
        (u : ℝ) * banditGap ν i ≤
          windowArmCenteredSum ν i lo hi h - windowArmCenteredSum ν j lo hi h} := by
    ext h
    simp [firstOptimalComparisonEvent, and_assoc]
  rw [hset]
  exact bandit_window_first_optimal_reference_comparison_tail
    ν hν (π := π) i hiGap lo hi u

private lemma lastOptimalEliminationWithSurvivor_mem_firstOptimalComparisonEvent
    {k n : ℕ} (ν : StochasticBandit k) (hn : k * Nat.clog 2 k ≤ n)
    (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) (i : Fin k) (h : BanditHistory k n)
    (hh : IsLastOptimalEliminationWithSurvivor k n ν h ℓ i) :
    h ∈ firstOptimalComparisonEvent (n := n) ν i
      (seqHalvingStart k n ℓ) (seqHalvingStart k n (ℓ + 1))
      (seqHalvingPulls k n ℓ) := by
  rcases lastOptimalEliminationWithSurvivor_imp_firstOptimalEvent
      ν hn ℓ hℓ i h hh with ⟨j, hjstate, hicount, hjcount, hmean⟩
  rw [firstOptimalComparisonEvent]
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
  refine ⟨j, ⟨⟨hjstate, ?_⟩, ?_⟩, ?_⟩
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hicount
  · rw [windowArmMass_seqHalvingPhase]
    exact_mod_cast hjcount
  · have hjgap : banditGap ν j = 0 := by
      rcases firstOptimalArmFrom_valid ν (seqHalvingStart k n ℓ)
        (seqHalvingStart k n (ℓ + 1)) h with hs | ⟨q, hqstate, hqgap⟩
      · exact (Fin.castSucc_ne_last j (hjstate.symm.trans hs)).elim
      · have hqj : q = j := by
          have hcode : Fin.castSucc q = Fin.castSucc j := hqstate.symm.trans hjstate
          apply Fin.ext
          exact congrArg (fun x : Fin (k + 1) ↦ x.val) hcode
        simpa [hqj] using hqgap
    rw [windowArmCenteredSum_seqHalvingPhase,
      windowArmCenteredSum_seqHalvingPhase, hicount, hjcount]
    have hu := seqHalvingPulls_pos_of_budget hn hℓ
    have huR : (0 : ℝ) < (seqHalvingPulls k n ℓ : ℝ) := by exact_mod_cast hu
    have hraw :
        (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) ≤
          ∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2 := by
      change
        (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = j), (h r).2) /
            (seqHalvingPulls k n ℓ : ℝ) ≤
          (∑ r ∈ (seqHalvingPhase k n ℓ).filter (fun r ↦ (h r).1 = i), (h r).2) /
            (seqHalvingPulls k n ℓ : ℝ) at hmean
      exact (div_le_div_iff_of_pos_right huR).mp hmean
    have hgapmean : banditGap ν i = banditArmMean ν j - banditArmMean ν i := by
      rw [banditGap] at hjgap ⊢
      linarith
    rw [hgapmean]
    nlinarith

private lemma measureReal_event_le_average_probabilities
    {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (F : ι → Set α)
    (hF : ∀ i, MeasurableSet (F i)) (c : ℝ) (hc : 0 < c)
    (hcount : ∀ x ∈ E, c ≤ ∑ i : ι, (F i).indicator (fun _ ↦ (1 : ℝ)) x) :
    μ.real E ≤ (∑ i : ι, μ.real (F i)) / c := by
  let N : α → ℝ := fun x ↦ ∑ i : ι, (F i).indicator (fun _ ↦ (1 : ℝ)) x
  have hNi (i : ι) : Integrable ((F i).indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (μ := μ) (1 : ℝ)).indicator (hF i)
  have hNint : Integrable N μ := by
    exact integrable_finset_sum Finset.univ (fun i _ ↦ hNi i)
  have hNnonneg : ∀ x, 0 ≤ N x := by
    intro x
    exact Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  have hmono : μ.real E ≤ μ.real {x | c ≤ N x} := by
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro x hx
    exact hcount x hx
  have hmarkov : c * μ.real {x | c ≤ N x} ≤ ∫ x, N x ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hNnonneg) hNint c
  have hint : (∫ x, N x ∂μ) = ∑ i : ι, μ.real (F i) := by
    simp only [N]
    rw [integral_finset_sum Finset.univ (fun i _ ↦ hNi i)]
    apply Finset.sum_congr rfl
    intro i _hi
    exact integral_indicator_one (hF i)
  rw [hint] at hmarkov
  apply (le_div_iff₀ hc).2
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono (le_of_lt hc)).trans hmarkov

theorem lastOptimalElimination_probability_le_threshold_tail_sum
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hn : k * Nat.clog 2 k ≤ n) (π : BanditPolicy k)
    (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) (threshold : ℕ)
    (hthreshold : threshold < seqHalvingCount k (ℓ + 1)) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingLastOptimalEliminationAt k n ν h ℓ} ≤
      (∑ i : Fin k,
        if threshold ≤ (i : ℕ) ∧ 0 < banditGap ν i then
          Real.exp (-(seqHalvingPulls k n ℓ : ℝ) * banditGap ν i ^ 2 / 4)
        else 0) / ((seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ) := by
  let lo := seqHalvingStart k n ℓ
  let hi := seqHalvingStart k n (ℓ + 1)
  let u := seqHalvingPulls k n ℓ
  let F : Fin k → Set (BanditHistory k n) := fun i ↦
    if threshold ≤ (i : ℕ) ∧ 0 < banditGap ν i then
      firstOptimalComparisonEvent (n := n) ν i lo hi u
    else ∅
  have hk : 0 < k := by
    have hp := Nat.pow_lt_of_lt_clog hℓ
    have hp0 : 0 < 2 ^ ℓ := pow_pos (by decide) _
    omega
  have hq : 0 < seqHalvingCount k (ℓ + 1) :=
    seqHalvingCount_pos k (ℓ + 1) hk
  have hc : (0 : ℝ) < ((seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hthreshold
  have hFmeas (i : Fin k) : MeasurableSet (F i) := by
    by_cases hcond : threshold ≤ (i : ℕ) ∧ 0 < banditGap ν i
    · simp only [F, hcond, if_true]
      exact measurableSet_firstOptimalComparisonEvent ν i lo hi u
    · simp [F, hcond]
  apply (measureReal_event_le_average_probabilities
    (banditMeasure ν π n)
    {h | IsSeqHalvingLastOptimalEliminationAt k n ν h ℓ} F
    hFmeas ((seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ) hc ?_).trans
  · apply div_le_div_of_nonneg_right _ (le_of_lt hc)
    apply Finset.sum_le_sum
    intro i _hi
    by_cases hcond : threshold ≤ (i : ℕ) ∧ 0 < banditGap ν i
    · dsimp [F, lo, hi, u]
      simp only [hcond, if_true]
      exact bandit_firstOptimalComparisonEvent_probability_bound
        ν hν (π := π) i hcond.2 _ _ _
    · dsimp [F, lo, hi, u]
      simp [hcond]
  · intro h hh
    rcases hh with ⟨A, hA0, hrun, hopt, hnextGap⟩
    have hcards := seqHalving_chain_card_eq_count A (Nat.clog 2 k) hA0
      (fun s hs ↦ (hrun s hs).2.1)
    have hcardm : (A ℓ).card = seqHalvingCount k ℓ := hcards ℓ (Nat.le_of_lt hℓ)
    have hcardq : (A (ℓ + 1)).card = seqHalvingCount k (ℓ + 1) :=
      hcards (ℓ + 1) hℓ
    let S := (A (ℓ + 1)).filter fun i : Fin k ↦ threshold ≤ (i : ℕ)
    let B := (A (ℓ + 1)).filter fun i : Fin k ↦ (i : ℕ) < threshold
    have hpart : S.card + B.card = (A (ℓ + 1)).card := by
      simpa [S, B, Nat.not_le] using
        (Finset.card_filter_add_card_filter_not
          (s := A (ℓ + 1)) (p := fun i : Fin k ↦ threshold ≤ (i : ℕ)))
    have hBsub : B ⊆ Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < threshold) := by
      intro i hiB
      simp only [B, Finset.mem_filter] at hiB
      simp [hiB.2]
    have hBcard : B.card ≤ threshold := by
      calc
        B.card ≤ (Finset.univ.filter (fun i : Fin k ↦ (i : ℕ) < threshold)).card :=
          Finset.card_le_card hBsub
        _ = min k threshold := Fin.card_filter_val_lt
        _ ≤ threshold := min_le_right _ _
    have hScard : ((seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ) ≤
        (S.card : ℝ) := by
      have hSnat : seqHalvingCount k (ℓ + 1) - threshold ≤ S.card := by
        rw [hcardq] at hpart
        omega
      exact_mod_cast hSnat
    calc
      ((seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ) ≤
          (S.card : ℝ) := hScard
      _ = ∑ i ∈ S, (F i).indicator (fun _ ↦ (1 : ℝ)) h := by
        calc
          (S.card : ℝ) = ∑ i ∈ S, (1 : ℝ) := by simp
          _ = ∑ i ∈ S, (F i).indicator (fun _ ↦ (1 : ℝ)) h := by
            apply Finset.sum_congr rfl
            intro i hiS
            have hiA : i ∈ A (ℓ + 1) := (Finset.mem_filter.mp hiS).1
            have hithreshold : threshold ≤ (i : ℕ) := (Finset.mem_filter.mp hiS).2
            have higap : 0 < banditGap ν i := hnextGap i hiA
            have hiwitness : IsLastOptimalEliminationWithSurvivor k n ν h ℓ i :=
              ⟨A, hA0, hrun, hopt, hnextGap, hiA⟩
            have hievent := lastOptimalEliminationWithSurvivor_mem_firstOptimalComparisonEvent
              ν hn ℓ hℓ i h hiwitness
            simp [F, hithreshold, higap, hievent, lo, hi, u]
      _ ≤ ∑ i : Fin k, (F i).indicator (fun _ ↦ (1 : ℝ)) h := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intro i _hi _hinot
        exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _

end BanditAlgorithm

open BanditAlgorithm

theorem solution
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingLastOptimalEliminationAt k n ν h ℓ} ≤
      3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  obtain ⟨threshold, hthreshold, htail⟩ :=
    sequential_halving_rank_tail_average_bound_clog_min
      (fun i ↦ banditGap ν i) hn H₂ hH₂ ℓ hℓ
  apply (le_min (measureReal_le_one)
    (BanditAlgorithm.lastOptimalElimination_probability_le_threshold_tail_sum
    ν hν hn π ℓ hℓ threshold hthreshold)).trans
  exact htail
