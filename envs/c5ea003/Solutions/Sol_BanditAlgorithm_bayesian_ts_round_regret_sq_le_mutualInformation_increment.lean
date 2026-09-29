-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_round_regret_sq_le_mutualInformation_increment
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:46:13.565727+00:00
-- url     : https://prove2.me/submissions/6eca4e0b-f2a0-4496-ac10-1c0ddb55352c

import Theorems.Thm_BanditAlgorithm_bayesian_ts_round_conditional_information_representation
import Mathlib.Analysis.Convex.Integral

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
      ∂bayesianAdversarialMeasure Q pi n le_rfl) ^ 2 ≤
      ((k : ℝ) / 2) *
        (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
          bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) := by
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
  let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
  have hhistory : Measurable history := by
    apply measurable_pi_lambda
    intro s
    exact (measurable_pi_apply (Fin.castLE (Nat.le_of_lt t.2) s)).comp measurable_snd
  letI : IsProbabilityMeasure nu := by
    dsimp [nu]
    exact Measure.isProbabilityMeasure_map hhistory.aemeasurable
  obtain ⟨r, info, hr, hrsq, hi, hregret, hpoint, htotal⟩ :=
    bayesian_ts_round_conditional_information_representation Q hQ hpi t
  rw [hregret]
  have hjensen : (∫ h, r h ∂nu) ^ 2 ≤ ∫ h, r h ^ 2 ∂nu := by
    exact (show Even 2 by decide).convexOn_pow.map_integral_le
      (continuousOn_pow 2) isClosed_univ
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
      hr (by simpa [Function.comp_def] using hrsq)
  calc
    (∫ h, r h ∂nu) ^ 2 ≤ ∫ h, r h ^ 2 ∂nu := hjensen
    _ ≤ ∫ h, ((k : ℝ) / 2) * info h ∂nu := integral_mono_ae hrsq (hi.const_mul _) hpoint
    _ = ((k : ℝ) / 2) * ∫ h, info h ∂nu := integral_const_mul _ _
    _ ≤ ((k : ℝ) / 2) *
        (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
          bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) := by
      gcongr

end BanditAlgorithm
