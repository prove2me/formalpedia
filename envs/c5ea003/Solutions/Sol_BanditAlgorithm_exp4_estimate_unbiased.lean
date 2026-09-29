-- Prove2me | solution 1 for BanditAlgorithm.exp4_estimate_unbiased
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T00:04:50.105378+00:00
-- url     : https://prove2.me/submissions/c0c4f77e-e6f7-4402-a697-44cdd1ae55cf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Policy

/-!
Direct proof following Lattimore--Szepesvári, *Bandit Algorithms*,
Theorem 18.1, printed p. 230, Eq. (18.10).  Conditional on the past, the
importance-weighted score increment of each fixed expert has expectation equal
to that expert's advice-weighted reward in the current round.
-/

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private lemma exp4Weights_pos_test {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (n : ℕ) (h : BanditHistory k n)
    (m : Fin M) :
    0 < exp4ExpertWeights η γ E n h m := by
  unfold exp4ExpertWeights
  rw [expWeights]
  apply div_pos (Real.exp_pos _)
  exact Finset.sum_pos' (fun j _ ↦ (Real.exp_pos _).le)
    ⟨m, Finset.mem_univ _, Real.exp_pos _⟩

private lemma sum_exp4Weights_test {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (n : ℕ) (h : BanditHistory k n)
    (m : Fin M) :
    ∑ j, exp4ExpertWeights η γ E n h j = 1 := by
  unfold exp4ExpertWeights
  rw [show
      (∑ j, expWeights
          (fun j ↦ η * exp4Estimate η γ E n h j) j) =
        (∑ j, Real.exp (η * exp4Estimate η γ E n h j)) /
          (∑ j, Real.exp (η * exp4Estimate η γ E n h j)) by
      simp only [expWeights, Finset.sum_div]]
  exact div_self (ne_of_gt (Finset.sum_pos'
    (fun j _ ↦ (Real.exp_pos _).le)
    ⟨m, Finset.mem_univ _, Real.exp_pos _⟩))

private lemma exp4Prob_nonneg_test {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (n : ℕ) (h : BanditHistory k n) (a : Fin k) :
    0 ≤ exp4Prob η γ E n h a := by
  unfold exp4Prob
  exact Finset.sum_nonneg fun m _ ↦
    mul_nonneg (exp4Weights_pos_test η γ E n h m).le (hE0 n m a)

private lemma sum_exp4Prob_test {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (n : ℕ) (h : BanditHistory k n) (m₀ : Fin M) :
    ∑ a, exp4Prob η γ E n h a = 1 := by
  calc
    (∑ a, exp4Prob η γ E n h a) =
        ∑ m, exp4ExpertWeights η γ E n h m * ∑ a, E n m a := by
      simp only [exp4Prob]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ m, exp4ExpertWeights η γ E n h m := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [hE1 n m, mul_one]
    _ = 1 := sum_exp4Weights_test η γ E n h m₀

private lemma exp4Prob_pos_of_advice_pos_test {k M : ℕ} (η γ : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (n : ℕ) (h : BanditHistory k n) (m : Fin M) (a : Fin k)
    (hEma : 0 < E n m a) :
    0 < exp4Prob η γ E n h a := by
  unfold exp4Prob
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (exp4Weights_pos_test η γ E n h j).le (hE0 n j a)
  · exact ⟨m, Finset.mem_univ _,
      mul_pos (exp4Weights_pos_test η γ E n h m) hEma⟩

private noncomputable def exp4Increment {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m : Fin M) (z : Fin k × ℝ) : ℝ :=
  ∑ a, E r m a *
    (1 - if z.1 = a then
      (1 - z.2) / exp4Prob η 0 E r h a
    else 0)

private lemma exp4Increment_measurable {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ)
    (h : BanditHistory k r) (m : Fin M) :
    Measurable (exp4Increment η E r h m) := by
  classical
  unfold exp4Increment
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.mul measurable_const
  apply Measurable.sub measurable_const
  have hset : MeasurableSet {z : Fin k × ℝ | z.1 = a} := by
    simpa only [Set.mem_singleton_iff] using
      (measurableSet_singleton a).preimage measurable_fst
  have hthen : Measurable (fun z : Fin k × ℝ ↦
      (1 - z.2) / exp4Prob η 0 E r h a) :=
    (measurable_const.sub measurable_snd).div_const _
  exact Measurable.ite hset hthen measurable_const

private lemma exp4Increment_integrable_step {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M) :
    Integrable (exp4Increment η E r h m) (adversarialStepKernel x π r h) := by
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h]
  apply (integrable_map_measure
    (exp4Increment_measurable η E r h m).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  exact Integrable.of_finite

private lemma exp4Increment_integral_step {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M) :
    ∫ z, exp4Increment η E r h m z ∂(adversarialStepKernel x π r h) =
      ∑ a, E r m a * x r a := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp4Increment_measurable η E r h m).aestronglyMeasurable]
  rw [hπ r h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have hp0 : ∀ a : Fin k, 0 ≤ exp4Prob η 0 E r h a :=
      fun a ↦ exp4Prob_nonneg_test η 0 E hE0 r h a
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal (hp0 a)
    simp_rw [htoReal]
    have hsum : ∑ a, exp4Prob η 0 E r h a = 1 :=
      sum_exp4Prob_test η 0 E hE1 r h m
    have hcomponent : ∀ a : Fin k,
        (∑ j, exp4Prob η 0 E r h j *
          (E r m a * (1 - if j = a then
            (1 - x r j) / exp4Prob η 0 E r h a
          else 0))) =
        E r m a * x r a := by
      intro a
      by_cases hEa : E r m a = 0
      · simp [hEa]
      · have hEa_pos : 0 < E r m a := lt_of_le_of_ne (hE0 r m a) (Ne.symm hEa)
        have hp : 0 < exp4Prob η 0 E r h a :=
          exp4Prob_pos_of_advice_pos_test η 0 E hE0 r h m a hEa_pos
        have hdecomp :
            (∑ j, exp4Prob η 0 E r h j *
              (1 - if j = a then
                (1 - x r j) / exp4Prob η 0 E r h a
              else 0)) =
            (∑ j, exp4Prob η 0 E r h j) -
              exp4Prob η 0 E r h a *
                ((1 - x r a) / exp4Prob η 0 E r h a) := by
          calc
            (∑ j, exp4Prob η 0 E r h j *
                (1 - if j = a then
                  (1 - x r j) / exp4Prob η 0 E r h a
                else 0)) =
                ∑ j, (exp4Prob η 0 E r h j -
                  if j = a then
                    exp4Prob η 0 E r h a *
                      ((1 - x r a) / exp4Prob η 0 E r h a)
                  else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hja : j = a
              · subst j
                simp
                ring
              · simp [hja]
            _ = (∑ j, exp4Prob η 0 E r h j) -
                  ∑ j, if j = a then
                    exp4Prob η 0 E r h a *
                      ((1 - x r a) / exp4Prob η 0 E r h a)
                  else 0 := by
              rw [Finset.sum_sub_distrib]
            _ = (∑ j, exp4Prob η 0 E r h j) -
                  exp4Prob η 0 E r h a *
                    ((1 - x r a) / exp4Prob η 0 E r h a) := by
              simp
        calc
          (∑ j, exp4Prob η 0 E r h j *
              (E r m a * (1 - if j = a then
                (1 - x r j) / exp4Prob η 0 E r h a
              else 0))) =
              E r m a * ∑ j, exp4Prob η 0 E r h j *
                (1 - if j = a then
                  (1 - x r j) / exp4Prob η 0 E r h a
                else 0) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = E r m a * x r a := by
            rw [hdecomp, hsum]
            field_simp [ne_of_gt hp]
            ring
    calc
      (∑ j, exp4Prob η 0 E r h j *
          exp4Increment η E r h m (j, x r j)) =
          ∑ j, ∑ a, exp4Prob η 0 E r h j *
            (E r m a * (1 - if j = a then
              (1 - x r j) / exp4Prob η 0 E r h a
            else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [exp4Increment, Finset.mul_sum]
      _ = ∑ a, ∑ j, exp4Prob η 0 E r h j *
            (E r m a * (1 - if j = a then
              (1 - x r j) / exp4Prob η 0 E r h a
            else 0)) := Finset.sum_comm
      _ = ∑ a, E r m a * x r a := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hcomponent a
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp4Estimate_measurable_test {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) :
    ∀ (r : ℕ) (m : Fin M),
      Measurable (fun h : BanditHistory k r ↦ exp4Estimate η 0 E r h m) := by
  intro r
  induction r with
  | zero =>
      intro m
      simp [exp4Estimate]
  | succ r ih =>
      intro m
      have hinit : Measurable
          (fun h : BanditHistory k (r + 1) ↦ Fin.init h) := by
        rw [measurable_pi_iff]
        intro t
        exact measurable_pi_apply (Fin.castSucc t)
      have hold : Measurable
          (fun h : BanditHistory k (r + 1) ↦
            exp4Estimate η 0 E r (Fin.init h) m) :=
        (ih m).comp hinit
      have hprob : ∀ a : Fin k, Measurable
          (fun h : BanditHistory k (r + 1) ↦
            exp4Prob η 0 E r (Fin.init h) a) := by
        intro a
        unfold exp4Prob exp4ExpertWeights expWeights
        apply Finset.measurable_sum
        intro j hj
        apply Measurable.mul
        · apply Measurable.div
          · exact Real.continuous_exp.measurable.comp
              (measurable_const.mul ((ih j).comp hinit))
          · apply Finset.measurable_sum
            intro q hq
            exact Real.continuous_exp.measurable.comp
              (measurable_const.mul ((ih q).comp hinit))
        · exact measurable_const
      have hlast : Measurable
          (fun h : BanditHistory k (r + 1) ↦ h (Fin.last r)) :=
        measurable_pi_apply (Fin.last r)
      have hinc : Measurable
          (fun h : BanditHistory k (r + 1) ↦
            ∑ a, E r m a *
              (1 - if (h (Fin.last r)).1 = a then
                (1 - (h (Fin.last r)).2) /
                  exp4Prob η 0 E r (Fin.init h) a
              else 0)) := by
        apply Finset.measurable_sum
        intro a ha
        apply Measurable.mul measurable_const
        apply Measurable.sub measurable_const
        have hcond : MeasurableSet
            {h : BanditHistory k (r + 1) | (h (Fin.last r)).1 = a} := by
          simpa only [Set.mem_singleton_iff] using
            (measurableSet_singleton a).preimage (measurable_fst.comp hlast)
        have hfrac : Measurable
            (fun h : BanditHistory k (r + 1) ↦
              (1 - (h (Fin.last r)).2) /
                exp4Prob η 0 E r (Fin.init h) a) :=
          (measurable_const.sub (measurable_snd.comp hlast)).div (hprob a)
        exact Measurable.ite hcond hfrac measurable_const
      simpa only [exp4Estimate, exp4Prob, exp4ExpertWeights, add_zero] using
        hold.add hinc

private lemma exp4Prob_measurable_test {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (a : Fin k) :
    Measurable (fun h : BanditHistory k r ↦ exp4Prob η 0 E r h a) := by
  unfold exp4Prob exp4ExpertWeights expWeights
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.mul
  · apply Measurable.div
    · exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_test η E r m))
    · apply Finset.measurable_sum
      intro j hj
      exact Real.continuous_exp.measurable.comp
        (measurable_const.mul (exp4Estimate_measurable_test η E r j))
  · exact measurable_const

private lemma exp4Increment_joint_measurable_test {k M : ℕ} (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ) (r : ℕ) (m : Fin M) :
    Measurable (fun p : BanditHistory k r × (Fin k × ℝ) ↦
      exp4Increment η E r p.1 m p.2) := by
  classical
  unfold exp4Increment
  apply Finset.measurable_sum
  intro a ha
  apply Measurable.mul measurable_const
  apply Measurable.sub measurable_const
  have hcond : MeasurableSet
      {p : BanditHistory k r × (Fin k × ℝ) | p.2.1 = a} := by
    simpa only [Set.mem_singleton_iff] using
      (measurableSet_singleton a).preimage
        (measurable_fst.comp measurable_snd)
  have hfrac : Measurable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        (1 - p.2.2) / exp4Prob η 0 E r p.1 a) :=
    (measurable_const.sub (measurable_snd.comp measurable_snd)).div
      ((exp4Prob_measurable_test η E r a).comp measurable_fst)
  exact Measurable.ite hcond hfrac measurable_const

private lemma exp4Increment_norm_integral_step_test {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M) :
    ∫ z, ‖exp4Increment η E r h m z‖ ∂(adversarialStepKernel x π r h) =
      ∑ a, exp4Prob η 0 E r h a *
        ‖exp4Increment η E r h m (a, x r a)‖ := by
  classical
  rw [adversarialStepKernel, Kernel.map_apply _ (measurable_of_countable _) h,
    integral_map (measurable_of_countable _).aemeasurable
      (exp4Increment_measurable η E r h m).norm.aestronglyMeasurable]
  rw [hπ r h]
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    have htoReal : ∀ a : Fin k,
        (ENNReal.ofReal (exp4Prob η 0 E r h a)).toReal =
          exp4Prob η 0 E r h a :=
      fun a ↦ ENNReal.toReal_ofReal
        (exp4Prob_nonneg_test η 0 E hE0 r h a)
    simp_rw [htoReal]
  · intro a ha
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

private lemma exp4Increment_at_reward_eq {k M : ℕ}
    (x : ℕ → Fin k → ℝ) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M) (j : Fin k) :
    exp4Increment η E r h m (j, x r j) =
      1 - E r m j * ((1 - x r j) / exp4Prob η 0 E r h j) := by
  classical
  unfold exp4Increment
  calc
    (∑ a, E r m a *
        (1 - if j = a then
          (1 - x r j) / exp4Prob η 0 E r h a
        else 0)) =
        ∑ a, (E r m a -
          if a = j then
            E r m j * ((1 - x r j) / exp4Prob η 0 E r h j)
          else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases haj : a = j
      · subst a
        simp
        ring
      · have hja : ¬j = a := fun h ↦ haj h.symm
        simp [haj, hja]
    _ = (∑ a, E r m a) -
          ∑ a, if a = j then
            E r m j * ((1 - x r j) / exp4Prob η 0 E r h j)
          else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - E r m j * ((1 - x r j) / exp4Prob η 0 E r h j) := by
      rw [hE1 r m]
      simp

private lemma exp4Increment_norm_integral_step_le_test {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (h : BanditHistory k r) (m : Fin M) :
    (∫ z, ‖exp4Increment η E r h m z‖
      ∂(adversarialStepKernel x π r h)) ≤ 2 := by
  classical
  rw [exp4Increment_norm_integral_step_test x π η E hE0 hπ r h m]
  have hsum : ∑ a, exp4Prob η 0 E r h a = 1 :=
    sum_exp4Prob_test η 0 E hE1 r h m
  calc
    (∑ a, exp4Prob η 0 E r h a *
        ‖exp4Increment η E r h m (a, x r a)‖) ≤
        ∑ a, (exp4Prob η 0 E r h a + E r m a) := by
      apply Finset.sum_le_sum
      intro a ha
      have hp0 : 0 ≤ exp4Prob η 0 E r h a :=
        exp4Prob_nonneg_test η 0 E hE0 r h a
      rw [exp4Increment_at_reward_eq x η E hE1 r h m a]
      by_cases hEa : E r m a = 0
      · simp [hEa, hp0]
      · have hEa_pos : 0 < E r m a :=
          lt_of_le_of_ne (hE0 r m a) (Ne.symm hEa)
        have hp : 0 < exp4Prob η 0 E r h a :=
          exp4Prob_pos_of_advice_pos_test η 0 E hE0 r h m a hEa_pos
        have hxloss : 0 ≤ 1 - x r a := sub_nonneg.mpr (hx r a).2
        simp only [Real.norm_eq_abs]
        calc
          exp4Prob η 0 E r h a *
              |1 - E r m a *
                ((1 - x r a) / exp4Prob η 0 E r h a)| ≤
              exp4Prob η 0 E r h a *
                (|1| + |E r m a *
                  ((1 - x r a) / exp4Prob η 0 E r h a)|) :=
            mul_le_mul_of_nonneg_left (abs_sub _ _) hp0
          _ = exp4Prob η 0 E r h a + E r m a * (1 - x r a) := by
            rw [abs_one, abs_mul, abs_div, abs_of_pos hEa_pos,
              abs_of_nonneg hxloss, abs_of_pos hp]
            field_simp [ne_of_gt hp]
          _ ≤ exp4Prob η 0 E r h a + E r m a := by
            nlinarith [mul_nonneg (hE0 r m a) (hx r a).1]
    _ = 2 := by
      rw [Finset.sum_add_distrib, hsum, hE1 r m]
      norm_num

private lemma exp4Increment_integrable_joint_test {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π)
    (r : ℕ) (m : Fin M) :
    Integrable
      (fun p : BanditHistory k r × (Fin k × ℝ) ↦
        exp4Increment η E r p.1 m p.2)
      ((adversarialMeasure x π r).compProd
        (adversarialStepKernel x π r)) := by
  apply (Measure.integrable_compProd_iff
    (exp4Increment_joint_measurable_test η E r m).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun h ↦
      exp4Increment_integrable_step x π η E r h m
  · apply Integrable.of_mem_Icc 0 2
    · exact (exp4Increment_joint_measurable_test η E r m).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'.aemeasurable
    · exact Filter.Eventually.of_forall fun h ↦ by
        constructor
        · exact integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun z ↦ norm_nonneg _)
        · exact exp4Increment_norm_integral_step_le_test
            x hx π η E hE0 hE1 hπ r h m

private theorem exp4Estimate_integrable_integral_test {k M : ℕ}
    (x : ℕ → Fin k → ℝ)
    (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (hπ : IsExp4Policy η 0 E π) :
    ∀ (r : ℕ) (m : Fin M),
      Integrable (fun h : BanditHistory k r ↦ exp4Estimate η 0 E r h m)
          (adversarialMeasure x π r) ∧
        (∫ h, exp4Estimate η 0 E r h m
            ∂(adversarialMeasure x π r)) =
          ∑ t : Fin r, ∑ a, E t m a * x t a := by
  intro r
  induction r with
  | zero =>
      intro m
      simp [exp4Estimate, adversarialMeasure]
  | succ r ih =>
      intro m
      let μ := adversarialMeasure x π r
      let κ := adversarialStepKernel x π r
      let snoc : BanditHistory k r × (Fin k × ℝ) →
          BanditHistory k (r + 1) :=
        fun p ↦ Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2
      have hsnoc : Measurable snoc := measurable_banditHistorySnoc
      have hrewrite :
          (fun p ↦ exp4Estimate η 0 E (r + 1) (snoc p) m) =
            fun p ↦ exp4Estimate η 0 E r p.1 m +
              exp4Increment η E r p.1 m p.2 := by
        funext p
        simp [snoc, exp4Estimate, exp4Increment, exp4Prob,
          exp4ExpertWeights]
      have hold : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4Estimate η 0 E r p.1 m)
          (μ.compProd κ) := by
        have hi : Integrable
            (fun h : BanditHistory k r ↦ exp4Estimate η 0 E r h m)
            (Measure.map Prod.fst (μ.compProd κ)) := by
          change Integrable
            (fun h : BanditHistory k r ↦ exp4Estimate η 0 E r h m)
            ((μ.compProd κ).fst)
          rw [Measure.fst_compProd]
          exact (ih m).1
        exact hi.comp_aemeasurable measurable_fst.aemeasurable
      have hnew : Integrable
          (fun p : BanditHistory k r × (Fin k × ℝ) ↦
            exp4Increment η E r p.1 m p.2)
          (μ.compProd κ) :=
        exp4Increment_integrable_joint_test
          x hx π η E hE0 hE1 hπ r m
      have hsum_integrable := hold.add hnew
      have hcomp : Integrable
          ((fun h : BanditHistory k (r + 1) ↦
            exp4Estimate η 0 E (r + 1) h m) ∘ snoc)
          (μ.compProd κ) := by
        change Integrable
          (fun p ↦ exp4Estimate η 0 E (r + 1) (snoc p) m)
          (μ.compProd κ)
        rw [hrewrite]
        exact hsum_integrable
      constructor
      · rw [adversarialMeasure]
        apply (integrable_map_measure
          (exp4Estimate_measurable_test η E (r + 1) m).aestronglyMeasurable
          hsnoc.aemeasurable).2
        exact hcomp
      · rw [adversarialMeasure,
          integral_map hsnoc.aemeasurable
            (exp4Estimate_measurable_test η E (r + 1) m).aestronglyMeasurable]
        change
          (∫ p, exp4Estimate η 0 E (r + 1) (snoc p) m
              ∂(μ.compProd κ)) =
            ∑ t : Fin (r + 1), ∑ a, E t m a * x t a
        rw [hrewrite, integral_add hold hnew,
          Measure.integral_compProd hold, Measure.integral_compProd hnew]
        rw [Fin.sum_univ_castSucc]
        simp [μ, κ, (ih m).2,
          exp4Increment_integral_step x π η E hE0 hE1 hπ]

end BanditAlgorithm

theorem solution
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, BanditAlgorithm.exp4Estimate η 0 E n h m
      ∂(BanditAlgorithm.adversarialMeasure x π n)) =
      BanditAlgorithm.expertTotalReward n x E m := by
  simpa [BanditAlgorithm.expertTotalReward] using
    (BanditAlgorithm.exp4Estimate_integrable_integral_test
      x hx π η E hE0 hE1 hπ n m).2
