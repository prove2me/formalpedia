-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_conditional_gains_information_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T03:18:58.18004+00:00
-- url     : https://prove2.me/submissions/e40d39d2-ef5e-4657-ba42-3c9ef372dcb4

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal
import Theorems.Thm_BanditAlgorithm_thompson_sampling_one_step_information_ratio_varying_reference
import Theorems.Thm_InformationTheory_conditional_finite_mutualInformation_integrable
import Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_diagonal_representation

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace BanditAlgorithm

private theorem measurable_optimal_final {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

private theorem map_fst_terminal_final {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) :
    Measure.map Prod.fst (bayesianAdversarialMeasure Q pi n le_rfl) = Q := by
  have hp := bayesianAdversarialMeasure_prefix_marginal Q pi n le_rfl 0 (Nat.zero_le n)
  have hprefix : Measurable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
        (p.1, fun s : Fin 0 ↦ p.2 (Fin.castLE (Nat.zero_le n) s))) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro s
    exact s.elim0
  have hmap := congrArg (Measure.map (@Prod.fst
    (Fin n → Fin k → ℝ) (BanditHistory k 0))) hp
  rw [Measure.map_map measurable_fst hprefix] at hmap
  calc
    Measure.map Prod.fst (bayesianAdversarialMeasure Q pi n le_rfl) =
        Measure.map Prod.fst (bayesianAdversarialMeasure Q pi 0 (Nat.zero_le n)) := by
      simpa [Function.comp_def] using hmap
    _ = Q := by
      rw [bayesianAdversarialMeasure, Measure.map_map]
      · simp [Function.comp_def]
      · exact measurable_fst
      · exact measurable_id.prodMk measurable_const

private theorem integrable_roundRegret_final
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    (pi : BanditPolicy k) (t : Fin n) :
    Integrable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
        p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
      (bayesianAdversarialMeasure Q pi n le_rfl) := by
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  have hopt : Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t (bayesianOptimalAction p.1)) := by
    have heval : Measurable
        (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    exact heval.comp (measurable_fst.prodMk
      (measurable_optimal_final.comp measurable_fst))
  have hplayed : Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t ((p.2 t).1)) := by
    have heval : Measurable
        (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    exact heval.comp (measurable_fst.prodMk
      (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)))
  have hset : MeasurableSet
      {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1} := by
    rw [show {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k),
        X s a ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ s : Fin n, ⋂ a : Fin k, {X | X s a ∈ Set.Icc (0 : ℝ) 1} by
      ext X
      simp]
    exact MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun a ↦
      measurableSet_Icc.preimage
        ((measurable_pi_apply a).comp (measurable_pi_apply s))
  have hbound : ∀ᵐ p ∂mu, ∀ (s : Fin n) (a : Fin k),
      p.1 s a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← ae_map_iff measurable_fst.aemeasurable hset,
      map_fst_terminal_final Q pi]
    exact hQ
  apply Integrable.of_bound (hopt.sub hplayed).aestronglyMeasurable 1
  filter_upwards [hbound] with p hp
  rw [Real.norm_eq_abs]
  have ho := hp t (bayesianOptimalAction p.1)
  have ha := hp t ((p.2 t).1)
  exact abs_le.2 ⟨by linarith [ho.1, ha.2], by linarith [ho.2, ha.1]⟩

private theorem regret_gain_integrable_final
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    (pi : BanditPolicy k) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    Integrable (bayesianTSRoundConditionalRegretGain Q pi t) nu ∧
      Integrable (fun h ↦ bayesianTSRoundConditionalRegretGain Q pi t h ^ 2) nu := by
  dsimp only
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let nu := Measure.map history mu
  let f := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1)
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hf : Integrable f mu := integrable_roundRegret_final Q hQ pi t
  have hfmeas : Measurable f := by
    have heval : Measurable
        (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    exact (heval.comp (measurable_fst.prodMk
      (measurable_optimal_final.comp measurable_fst))).sub
      (heval.comp (measurable_fst.prodMk
        (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd))))
  have hfmap : Integrable
      (fun z : BanditHistory k t.1 ×
        ((Fin n → Fin k → ℝ) × BanditHistory k n) ↦ f z.2)
      (mu.map (fun p ↦ (history p, p))) := by
    apply (integrable_map_measure
      (hf.1.comp_snd_map_prodMk history)
      (hhistory.aemeasurable.prodMk aemeasurable_id)).2
    simpa [Function.comp_def] using hf
  have hr : Integrable (fun h ↦ ∫ p, f p ∂condDistrib id history mu h) nu := by
    have := hfmap.integral_condDistrib_map (X := history) (Y := id) aemeasurable_id
    simpa [nu, Function.comp_def] using this
  have hnorm : Integrable (fun h ↦ ‖∫ p, f p ∂condDistrib id history mu h‖) nu := by
    have := hfmap.norm_integral_condDistrib_map (X := history) (Y := id) aemeasurable_id
    simpa [nu, Function.comp_def] using this
  have hrewardBound : ∀ᵐ p ∂mu, ∀ (s : Fin n) (a : Fin k),
      p.1 s a ∈ Set.Icc (0 : ℝ) 1 := by
    have hset : MeasurableSet
        {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k),
          X s a ∈ Set.Icc (0 : ℝ) 1} := by
      rw [show {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k),
          X s a ∈ Set.Icc (0 : ℝ) 1} =
          ⋂ s : Fin n, ⋂ a : Fin k, {X | X s a ∈ Set.Icc (0 : ℝ) 1} by
        ext X
        simp]
      exact MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun a ↦
        measurableSet_Icc.preimage
          ((measurable_pi_apply a).comp (measurable_pi_apply s))
    rw [← ae_map_iff measurable_fst.aemeasurable hset,
      map_fst_terminal_final Q pi]
    exact hQ
  have hfnorm : ∀ᵐ p ∂mu, ‖f p‖ ≤ 1 := by
    filter_upwards [hrewardBound] with p hp
    rw [Real.norm_eq_abs]
    have ho := hp t (bayesianOptimalAction p.1)
    have ha := hp t ((p.2 t).1)
    exact abs_le.2 ⟨by linarith [ho.1, ha.2], by linarith [ho.2, ha.1]⟩
  have hpair : nu ⊗ₘ condDistrib id history mu =
      mu.map (fun p ↦ (history p, p)) := by
    exact compProd_map_condDistrib aemeasurable_id
  have hpairBound : ∀ᵐ z ∂nu ⊗ₘ condDistrib id history mu, ‖f z.2‖ ≤ 1 := by
    rw [hpair]
    have hm : Measurable (fun p ↦ (history p, p)) :=
      hhistory.prodMk measurable_id
    have hs : MeasurableSet
        {z : BanditHistory k t.1 ×
          ((Fin n → Fin k → ℝ) × BanditHistory k n) | ‖f z.2‖ ≤ 1} :=
      measurableSet_le (hfmeas.norm.comp measurable_snd) measurable_const
    apply (ae_map_iff hm.aemeasurable hs).2
    simpa only using hfnorm
  have hlocalBound : ∀ᵐ h ∂nu, ∀ᵐ p ∂condDistrib id history mu h,
      ‖f p‖ ≤ 1 := Measure.ae_ae_of_ae_compProd hpairBound
  have hbound : ∀ᵐ h ∂nu, ‖∫ p, f p ∂condDistrib id history mu h‖ ≤ 1 := by
    have hlocal := hfmap.condDistrib_ae_map (X := history) (Y := id) aemeasurable_id
    filter_upwards [hlocal, hlocalBound] with h hh hb
    calc
      ‖∫ p, f p ∂condDistrib id history mu h‖ ≤
          ∫ p, ‖f p‖ ∂condDistrib id history mu h := norm_integral_le_integral_norm _
      _ ≤ 1 := by
        haveI : IsProbabilityMeasure (condDistrib id history mu h) := inferInstance
        exact (integral_mono_ae hh.norm (integrable_const 1) hb).trans_eq (by simp)
  have hrsq : Integrable (fun h ↦ (∫ p, f p ∂condDistrib id history mu h) ^ 2) nu := by
    apply Integrable.of_bound (hr.1.pow 2) 1
    filter_upwards [hbound] with h hh
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have habs : |∫ p, f p ∂condDistrib id history mu h| ≤ 1 := by
      simpa [Real.norm_eq_abs] using hh
    change (∫ p, f p ∂condDistrib id history mu h) ^ 2 ≤ 1
    have hs := mul_self_le_mul_self
      (abs_nonneg (∫ p, f p ∂condDistrib id history mu h)) habs
    simpa [pow_two] using hs
  simpa [bayesianTSRoundConditionalRegretGain, mu, history, nu, f] using ⟨hr, hrsq⟩

private theorem information_gain_integrable_final
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    Integrable (bayesianTSRoundConditionalInformationGain Q pi t) nu := by
  dsimp only
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let optimal := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    bayesianOptimalAction p.1
  let observation := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦ p.2 t
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  have hoptimal : Measurable optimal := measurable_optimal_final.comp measurable_fst
  have hobservation : Measurable observation :=
    (measurable_pi_apply t).comp measurable_snd
  have hi := conditional_finite_mutualInformation_integrable
    mu history observation optimal hhistory hobservation hoptimal
  simpa [bayesianTSRoundConditionalInformationGain, mu, history, optimal, observation] using hi

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    Integrable (bayesianTSRoundConditionalRegretGain Q pi t) nu ∧
      Integrable (fun h ↦ bayesianTSRoundConditionalRegretGain Q pi t h ^ 2) nu ∧
      Integrable (bayesianTSRoundConditionalInformationGain Q pi t) nu ∧
      (∀ᵐ h ∂nu,
        bayesianTSRoundConditionalRegretGain Q pi t h ^ 2 ≤
          ((k : ℝ) / 2) * bayesianTSRoundConditionalInformationGain Q pi t h) := by
  dsimp only
  obtain ⟨hr, hrsq⟩ := regret_gain_integrable_final Q hQ pi t
  refine ⟨hr, hrsq, information_gain_integrable_final Q pi t, ?_⟩
  filter_upwards [bayesian_ts_conditional_diagonal_representation Q hQ hpi t]
    with h hw
  obtain ⟨p, P, M, hP, hM, hfinite, hregret, hinfo⟩ := hw
  letI (a : Fin k) : IsProbabilityMeasure (P a) := hP a
  letI (a : Fin k) : IsProbabilityMeasure (M a) := hM a
  rw [hregret]
  have hdiag := thompson_sampling_one_step_information_ratio_varying_reference
    p P M (fun _ z ↦ z.1)
    (fun _ ↦ by fun_prop)
    (fun _ z ↦ z.2.1)
    (fun _ z ↦ z.2.2)
    hfinite
  exact hdiag.trans (mul_le_mul_of_nonneg_left hinfo (by positivity))

end BanditAlgorithm
