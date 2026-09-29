-- Prove2me | solution 1 for BanditAlgorithm.exp3_estimate_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-18T19:42:30.780418+00:00
-- url     : https://prove2.me/submissions/d5e2dd5c-bb07-4ea5-b301-7f1ef14e55dc

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

/-!
Direct proof work following Lattimore--Szepesvári, *Bandit Algorithms*,
§11.2 Eq. (11.6), printed p. 151, and the unbiasedness calculation in
Eq. (11.8), printed p. 153.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma expWeights_pos_test {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    0 < expWeights s i := by
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le) ⟨i, Finset.mem_univ _, Real.exp_pos _⟩

private lemma sum_expWeights_test {k : ℕ} (s : Fin k → ℝ) (i : Fin k) :
    ∑ j, expWeights s j = 1 := by
  rw [show (∑ j, expWeights s j) = (∑ j, Real.exp (s j)) / (∑ j, Real.exp (s j)) by
    simp only [expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨i, Finset.mem_univ _, Real.exp_pos _⟩))

private noncomputable def exp3Increment {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) (z : Fin k × ℝ) : ℝ :=
  1 - if z.1 = i then
    (1 - z.2) / exp3Prob η m h i
  else 0

private lemma exp3Increment_measurable {k : ℕ} (η : ℝ) (m : ℕ)
    (h : BanditHistory k m) (i : Fin k) :
    Measurable (exp3Increment η m h i) := by
  letI : DecidableEq (Fin k) := Classical.decEq _
  unfold exp3Increment
  apply Measurable.sub measurable_const
  have hnum : Measurable (fun z : Fin k × ℝ ↦ (1 : ℝ) - z.2) :=
    measurable_const.sub measurable_snd
  have hset : MeasurableSet {z : Fin k × ℝ | z.1 = i} := by
    simpa only [Set.mem_singleton_iff] using
      (measurableSet_singleton i).preimage measurable_fst
  have hthen : Measurable (fun z : Fin k × ℝ ↦
      (1 - z.2) / exp3Prob η m h i) := hnum.div_const _
  exact Measurable.ite hset hthen measurable_const

private lemma exp3Increment_integrable_step {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    Integrable (exp3Increment η m h i) (adversarialStepKernel x π m h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp3Increment_measurable η m h i).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp3Increment_integral_step {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    ∫ z, exp3Increment η m h i z ∂(adversarialStepKernel x π m h) = x m i := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp3Increment_measurable η m h i).aestronglyMeasurable]
  rw [hπ m h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have hp : 0 < exp3Prob η m h i := expWeights_pos_test _ i
    have hsum : ∑ j, exp3Prob η m h j = 1 := sum_expWeights_test _ i
    have htoReal : ∀ j : Fin k,
        (ENNReal.ofReal (exp3Prob η m h j)).toReal = exp3Prob η m h j :=
      fun j ↦ ENNReal.toReal_ofReal (expWeights_pos_test _ j).le
    simp_rw [htoReal]
    have hdecomp :
        (∑ j, exp3Prob η m h j *
          exp3Increment η m h i (j, x m j)) =
        (∑ j, exp3Prob η m h j) -
          exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i) := by
      calc
        (∑ j, exp3Prob η m h j * exp3Increment η m h i (j, x m j)) =
            (∑ j, exp3Prob η m h j) -
              ∑ j, if j = i then
                exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i)
              else 0 := by
                change (∑ j ∈ Finset.univ, exp3Prob η m h j *
                    exp3Increment η m h i (j, x m j)) =
                  (∑ j ∈ Finset.univ, exp3Prob η m h j) -
                    ∑ j ∈ Finset.univ, if j = i then
                      exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i)
                    else 0
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro j hj
                by_cases hji : j = i
                · subst j
                  simp [exp3Increment]
                  ring
                · simp [exp3Increment, hji]
        _ = (∑ j, exp3Prob η m h j) -
              exp3Prob η m h i * ((1 - x m i) / exp3Prob η m h i) := by
                simp
    rw [hdecomp, hsum]
    field_simp
    ring
  · intro j hj
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3Estimate_measurable_test {k : ℕ} (η : ℝ) :
    ∀ (m : ℕ) (i : Fin k),
      Measurable (fun h : BanditHistory k m ↦ exp3Estimate η m h i) := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [exp3Estimate]
  | succ m ih =>
      intro i
      have hinit : Measurable
          (fun h : BanditHistory k (m + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hold : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            exp3Estimate η m (Fin.init h) i) := (ih i).comp hinit
      have hprob : Measurable
          (fun h : BanditHistory k (m + 1) ↦ exp3Prob η m (Fin.init h) i) := by
        unfold exp3Prob expWeights
        apply Measurable.div
        · exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih i).comp hinit))
        · apply Finset.measurable_sum
          intro j hj
          exact Real.continuous_exp.measurable.comp
            (measurable_const.mul ((ih j).comp hinit))
      have hlast : Measurable
          (fun h : BanditHistory k (m + 1) ↦ h (Fin.last m)) :=
        measurable_pi_apply (Fin.last m)
      have hcond : MeasurableSet
          {h : BanditHistory k (m + 1) | (h (Fin.last m)).1 = i} := by
        simpa only [Set.mem_singleton_iff] using
          (measurableSet_singleton i).preimage (measurable_fst.comp hlast)
      have hfrac : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            (1 - (h (Fin.last m)).2) / exp3Prob η m (Fin.init h) i) :=
        (measurable_const.sub (measurable_snd.comp hlast)).div hprob
      have hinc : Measurable
          (fun h : BanditHistory k (m + 1) ↦
            1 - if (h (Fin.last m)).1 = i then
              (1 - (h (Fin.last m)).2) / exp3Prob η m (Fin.init h) i
            else 0) := by
        apply Measurable.sub measurable_const
        exact Measurable.ite hcond hfrac measurable_const
      simpa only [exp3Estimate, exp3Prob] using hold.add hinc

private lemma exp3Prob_measurable_test {k : ℕ} (η : ℝ) (m : ℕ) (i : Fin k) :
    Measurable (fun h : BanditHistory k m ↦ exp3Prob η m h i) := by
  unfold exp3Prob expWeights
  apply Measurable.div
  · exact Real.continuous_exp.measurable.comp
      (measurable_const.mul (exp3Estimate_measurable_test η m i))
  · apply Finset.measurable_sum
    intro j hj
    exact Real.continuous_exp.measurable.comp
      (measurable_const.mul (exp3Estimate_measurable_test η m j))

private lemma exp3Increment_joint_measurable_test {k : ℕ} (η : ℝ) (m : ℕ)
    (i : Fin k) :
    Measurable (fun p : BanditHistory k m × (Fin k × ℝ) ↦
      exp3Increment η m p.1 i p.2) := by
  classical
  unfold exp3Increment
  have hcond : MeasurableSet
      {p : BanditHistory k m × (Fin k × ℝ) | p.2.1 = i} := by
    simpa only [Set.mem_singleton_iff] using
      (measurableSet_singleton i).preimage (measurable_fst.comp measurable_snd)
  have hfrac : Measurable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        (1 - p.2.2) / exp3Prob η m p.1 i) :=
    (measurable_const.sub (measurable_snd.comp measurable_snd)).div
      ((exp3Prob_measurable_test η m i).comp measurable_fst)
  apply Measurable.sub measurable_const
  exact Measurable.ite hcond hfrac measurable_const

private lemma exp3Increment_norm_integral_step_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (hπ : IsExp3Policy η π) (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    ∫ z, ‖exp3Increment η m h i z‖ ∂(adversarialStepKernel x π m h) =
      ∑ j, exp3Prob η m h j * ‖exp3Increment η m h i (j, x m j)‖ := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp3Increment_measurable η m h i).norm.aestronglyMeasurable]
  rw [hπ m h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ j : Fin k,
        (ENNReal.ofReal (exp3Prob η m h j)).toReal = exp3Prob η m h j :=
      fun j ↦ ENNReal.toReal_ofReal (expWeights_pos_test _ j).le
    simp_rw [htoReal]
  · intro j hj
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp3Increment_norm_integral_step_le_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (h : BanditHistory k m) (i : Fin k) :
    (∫ z, ‖exp3Increment η m h i z‖ ∂(adversarialStepKernel x π m h)) ≤ 2 := by
  classical
  rw [exp3Increment_norm_integral_step_test x π η hπ m h i]
  have hsum : ∑ j, exp3Prob η m h j = 1 := sum_expWeights_test _ i
  calc
    (∑ j, exp3Prob η m h j * ‖exp3Increment η m h i (j, x m j)‖) ≤
        ∑ j, (exp3Prob η m h j + if j = i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hp : 0 < exp3Prob η m h j := expWeights_pos_test _ j
      by_cases hji : j = i
      · subst j
        simp only [if_pos]
        have hxi0 : 0 ≤ 1 - x m i := sub_nonneg.mpr (hx m i).2
        have hxi1 : 1 - x m i ≤ 1 := by linarith [(hx m i).1]
        simp only [exp3Increment, if_pos, Real.norm_eq_abs]
        change exp3Prob η m h i * |1 - (1 - x m i) / exp3Prob η m h i| ≤
          exp3Prob η m h i + 1
        calc
          exp3Prob η m h i * |1 - (1 - x m i) / exp3Prob η m h i| ≤
              exp3Prob η m h i *
                (|1| + |(1 - x m i) / exp3Prob η m h i|) :=
            mul_le_mul_of_nonneg_left (abs_sub _ _) hp.le
          _ = exp3Prob η m h i + (1 - x m i) := by
            rw [abs_one, abs_div, abs_of_nonneg hxi0, abs_of_pos hp]
            field_simp
          _ ≤ exp3Prob η m h i + 1 := by linarith
      · simp [exp3Increment, hji, hp.le]
    _ = 2 := by
      rw [Finset.sum_add_distrib]
      simp [hsum]
      norm_num

private lemma exp3Increment_integrable_joint_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π)
    (m : ℕ) (i : Fin k) :
    Integrable
      (fun p : BanditHistory k m × (Fin k × ℝ) ↦
        exp3Increment η m p.1 i p.2)
      ((adversarialMeasure x π m).compProd (adversarialStepKernel x π m)) := by
  apply (Measure.integrable_compProd_iff
    (exp3Increment_joint_measurable_test η m i).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp3Increment_integrable_step x π η hπ m h i
  · apply Integrable.of_mem_Icc 0 2
    · exact (exp3Increment_joint_measurable_test η m i).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp3Increment_norm_integral_step_le_test x hx π η hπ m h i

private theorem exp3Estimate_integrable_integral_test {k : ℕ}
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ j : Fin k, x t j ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hπ : IsExp3Policy η π) :
    ∀ (m : ℕ) (i : Fin k),
      Integrable (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
          (adversarialMeasure x π m) ∧
        (∫ h, exp3Estimate η m h i ∂(adversarialMeasure x π m)) =
          ∑ t : Fin m, x t i := by
  intro m
  induction m with
  | zero =>
      intro i
      simp [exp3Estimate, adversarialMeasure]
  | succ m ih =>
      intro i
      let μ := adversarialMeasure x π m
      let κ := adversarialStepKernel x π m
      let snoc : BanditHistory k m × (Fin k × ℝ) → BanditHistory k (m + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hrewrite :
          (fun p ↦ exp3Estimate η (m + 1) (snoc p) i) =
            fun p ↦ exp3Estimate η m p.1 i + exp3Increment η m p.1 i p.2 := by
        funext p
        simp [snoc, exp3Estimate, exp3Increment, exp3Prob]
      have hold : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3Estimate η m p.1 i)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable (fun h : BanditHistory k m ↦ exp3Estimate η m h i)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact (ih i).1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew : Integrable
          (fun p : BanditHistory k m × (Fin k × ℝ) ↦ exp3Increment η m p.1 i p.2)
          (μ.compProd κ) := exp3Increment_integrable_joint_test x hx π η hπ m i
      have hsum := hold.add hnew
      have hcomp : Integrable
          ((fun h : BanditHistory k (m + 1) ↦ exp3Estimate η (m + 1) h i) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable (fun p ↦ exp3Estimate η (m + 1) (snoc p) i)
          (μ.compProd κ)
        rw [hrewrite]
        exact hsum
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp3Estimate_measurable_test η (m + 1) i).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hcomp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp3Estimate_measurable_test η (m + 1) i).aestronglyMeasurable]
        change (∫ p, exp3Estimate η (m + 1) (snoc p) i ∂(μ.compProd κ)) =
          ∑ t : Fin (m + 1), x t i
        rw [hrewrite, integral_add hold hnew,
          Measure.integral_compProd hold, Measure.integral_compProd hnew]
        rw [Fin.sum_univ_castSucc]
        simp [μ, κ, (ih i).2, exp3Increment_integral_step x π η hπ]

end BanditAlgorithm

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditAlgorithm.BanditPolicy k) (η : ℝ) (hη : 0 < η)
    (hπ : BanditAlgorithm.IsExp3Policy η π) (i : Fin k) :
    (∫ h, BanditAlgorithm.exp3Estimate η n h i
      ∂(BanditAlgorithm.adversarialMeasure x π n)) = ∑ t : Fin n, x t i := by
  exact (BanditAlgorithm.exp3Estimate_integrable_integral_test x hx π η hπ n i).2
