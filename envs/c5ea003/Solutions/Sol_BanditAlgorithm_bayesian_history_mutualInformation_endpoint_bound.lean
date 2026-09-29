-- Prove2me | solution 1 for BanditAlgorithm.bayesian_history_mutualInformation_endpoint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T23:55:25.378587+00:00
-- url     : https://prove2.me/submissions/8ee69dc6-b0d5-481f-a62d-109612714633

import Definitions.Def_BayesianHistoryMutualInformation
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_log_card

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

private theorem measurable_bayesianOptimalAction_endpoint {k n : ℕ} [NeZero k] :
    Measurable (bayesianOptimalAction : (Fin n → Fin k → ℝ) → Fin k) := by
  apply measurable_minArgmax.comp
  apply measurable_pi_lambda
  intro a
  exact Finset.measurable_sum Finset.univ fun t _ ↦
    (measurable_pi_apply a).comp (measurable_pi_apply t)

theorem _root_.solution {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (pi : BanditPolicy k) :
    bayesianHistoryMutualInformation Q pi n le_rfl -
        bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n) ≤ Real.log k := by
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let historyN := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin n ↦ p.2 (Fin.castLE le_rfl s)
  let optimal := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    bayesianOptimalAction p.1
  have hhistoryN : Measurable historyN := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE le_rfl s)).comp measurable_snd
  have hoptimal : Measurable optimal :=
    measurable_bayesianOptimalAction_endpoint.comp measurable_fst
  have hterminal := finite_range_mutualInformation_le_log_card
    mu historyN optimal hhistoryN hoptimal
  have hinitial : 0 ≤ bayesianHistoryMutualInformation Q pi 0 (Nat.zero_le n) := by
    unfold bayesianHistoryMutualInformation
    positivity
  have hterminal_eq :
      bayesianHistoryMutualInformation Q pi n le_rfl =
        (klDiv (Measure.map (fun x ↦ (historyN x, optimal x)) mu)
          ((Measure.map historyN mu).prod (Measure.map optimal mu))).toReal := by
    rfl
  rw [hterminal_eq]
  linarith

end BanditAlgorithm
