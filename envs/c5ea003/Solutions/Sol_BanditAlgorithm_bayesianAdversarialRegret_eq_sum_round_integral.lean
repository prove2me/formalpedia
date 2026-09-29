-- Prove2me | solution 1 for BanditAlgorithm.bayesianAdversarialRegret_eq_sum_round_integral
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:51:22.526898+00:00
-- url     : https://prove2.me/submissions/a37d8d32-0d86-4475-b518-bb200508ae5a

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

private theorem map_fst_bayesianAdversarialMeasure {k n : ℕ}
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) (t : ℕ) (ht : t ≤ n) :
    Measure.map Prod.fst (bayesianAdversarialMeasure Q pi t ht) = Q := by
  induction t with
  | zero =>
      rw [bayesianAdversarialMeasure, Measure.map_map]
      · simp [Function.comp_def]
      · exact measurable_fst
      · exact measurable_id.prodMk measurable_const
  | succ t ih =>
      rw [bayesianAdversarialMeasure, Measure.map_map]
      · change Measure.map (fun p ↦ p.1.1)
          ((bayesianAdversarialMeasure Q pi t (Nat.le_of_succ_le ht)).compProd
            (bayesianAdversarialStepKernel pi t ⟨t, ht⟩)) = Q
        rw [show (fun p ↦ p.1.1) = Prod.fst ∘ Prod.fst by rfl]
        rw [← Measure.map_map measurable_fst measurable_fst]
        change
          (((bayesianAdversarialMeasure Q pi t (Nat.le_of_succ_le ht)).compProd
            (bayesianAdversarialStepKernel pi t ⟨t, ht⟩)).fst).fst = Q
        rw [Measure.fst_compProd]
        exact ih (Nat.le_of_succ_le ht)
      · exact measurable_fst
      · exact (measurable_fst.comp measurable_fst).prodMk
          (measurable_banditHistorySnoc.comp
            ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

private theorem measurable_bayesianOptimalAction {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

private theorem measurable_round_optimal_reward {k n : ℕ} [NeZero k] (t : Fin n) :
    Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t (bayesianOptimalAction p.1)) := by
  have heval : Measurable (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
    measurable_from_prod_countable_left fun a ↦
      (measurable_pi_apply a).comp (measurable_pi_apply t)
  exact heval.comp (measurable_fst.prodMk
    (measurable_bayesianOptimalAction.comp measurable_fst))

private theorem measurable_round_played_reward {k n : ℕ} (t : Fin n) :
    Measurable (fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      p.1 t ((p.2 t).1)) := by
  have heval : Measurable (fun p : (Fin n → Fin k → ℝ) × Fin k ↦ p.1 t p.2) :=
    measurable_from_prod_countable_left fun a ↦
      (measurable_pi_apply a).comp (measurable_pi_apply t)
  exact heval.comp (measurable_fst.prodMk
    (measurable_fst.comp ((measurable_pi_apply t).comp measurable_snd)))

theorem _root_.solution {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    (pi : BanditPolicy k) :
    bayesianAdversarialRegret Q pi =
      ∑ t, ∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
        ∂bayesianAdversarialMeasure Q pi n le_rfl := by
  unfold bayesianAdversarialRegret
  rw [integral_finset_sum]
  intro t _
  have hset : MeasurableSet
      {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1} := by
    rw [show {X : Fin n → Fin k → ℝ | ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1} =
        ⋂ s : Fin n, ⋂ a : Fin k, {X | X s a ∈ Set.Icc (0 : ℝ) 1} by
      ext X
      simp]
    exact MeasurableSet.iInter fun s ↦ MeasurableSet.iInter fun a ↦
      measurableSet_Icc.preimage ((measurable_pi_apply a).comp (measurable_pi_apply s))
  have hbound : ∀ᵐ p ∂bayesianAdversarialMeasure Q pi n le_rfl,
      ∀ (s : Fin n) (a : Fin k), p.1 s a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← ae_map_iff measurable_fst.aemeasurable hset,
      map_fst_bayesianAdversarialMeasure Q pi n le_rfl]
    exact hQ
  apply Integrable.of_bound
    ((measurable_round_optimal_reward t).sub (measurable_round_played_reward t)).aestronglyMeasurable 1
  filter_upwards [hbound] with p hp
  rw [Real.norm_eq_abs]
  have hopt := hp t (bayesianOptimalAction p.1)
  have hplay := hp t ((p.2 t).1)
  exact abs_le.2 ⟨by linarith [hopt.1, hplay.2], by linarith [hopt.2, hplay.1]⟩

end BanditAlgorithm
