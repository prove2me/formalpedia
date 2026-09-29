-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_conditional_regret_gain_integral
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T01:49:08.59429+00:00
-- url     : https://prove2.me/submissions/48eeb493-473c-4901-95d0-84438f4e9a81

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_bayesianAdversarialMeasure_prefix_marginal

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem measurable_optimal_accounting {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

private theorem map_fst_terminal_accounting {k n : ℕ}
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

private theorem integrable_roundRegret_accounting
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    (pi : BanditPolicy k) (t : Fin n) :
    Integrable
      (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
        p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
      (bayesianAdversarialMeasure Q pi n le_rfl) := by
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let f := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1)
  have hopt : Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t (bayesianOptimalAction p.1)) := by
    have heval : Measurable
        (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    exact heval.comp (measurable_fst.prodMk
      (measurable_optimal_accounting.comp measurable_fst))
  have hplayed : Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t ((p.2 t).1)) := by
    have heval : Measurable
        (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
      measurable_from_prod_countable_left fun a ↦
        (measurable_pi_apply a).comp (measurable_pi_apply t)
    exact heval.comp (measurable_fst.prodMk
      (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)))
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
  have hbound : ∀ᵐ p ∂mu, ∀ (s : Fin n) (a : Fin k),
      p.1 s a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← ae_map_iff measurable_fst.aemeasurable hset,
      map_fst_terminal_accounting Q pi]
    exact hQ
  apply Integrable.of_bound (hopt.sub hplayed).aestronglyMeasurable 1
  filter_upwards [hbound] with p hp
  rw [Real.norm_eq_abs]
  have ho := hp t (bayesianOptimalAction p.1)
  have ha := hp t ((p.2 t).1)
  exact abs_le.2 ⟨by linarith [ho.1, ha.2], by linarith [ho.2, ha.1]⟩

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
        ∂bayesianAdversarialMeasure Q pi n le_rfl) =
      ∫ h, bayesianTSRoundConditionalRegretGain Q pi t h ∂nu := by
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
  have hf : Integrable f mu := integrable_roundRegret_accounting Q hQ pi t
  have hpair : nu ⊗ₘ condDistrib id history mu =
      mu.map (fun p ↦ (history p, p)) := by
    exact compProd_map_condDistrib aemeasurable_id
  have hfmap : Integrable (fun z : BanditHistory k t.1 ×
      ((Fin n → Fin k → ℝ) × BanditHistory k n) ↦ f z.2)
      (mu.map (fun p ↦ (history p, p))) := by
    apply (integrable_map_measure (hf.1.comp_snd_map_prodMk history)
      (hhistory.aemeasurable.prodMk aemeasurable_id)).2
    simpa [Function.comp_def] using hf
  have hfcomp : Integrable (fun z : BanditHistory k t.1 ×
      ((Fin n → Fin k → ℝ) × BanditHistory k n) ↦ f z.2)
      (nu ⊗ₘ condDistrib id history mu) := by
    rwa [hpair]
  change (∫ p, f p ∂mu) =
    ∫ h, (∫ p, f p ∂condDistrib id history mu h) ∂nu
  rw [← Measure.integral_compProd hfcomp, hpair]
  exact (integral_map (hhistory.aemeasurable.prodMk aemeasurable_id) hfmap.1).symm

end BanditAlgorithm
