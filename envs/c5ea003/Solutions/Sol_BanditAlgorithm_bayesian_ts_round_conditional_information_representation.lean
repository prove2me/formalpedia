-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_round_conditional_information_representation
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T01:40:15.337823+00:00
-- url     : https://prove2.me/submissions/5d4308d3-b8c7-4664-99b5-11788d86ba0f

import Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_gains_information_ratio
import Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_gains_accounting

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-!
Source: Lattimore--Szepesvari, *Bandit Algorithms* (2020), Lemma 36.7,
printed p. 470 / free PDF p. 479.  This is a purely formal bridge collecting
the lemma's conditional information-ratio estimate and its disintegration /
chain-rule accounting, using the canonical conditional gains defined in
`Def_BayesianTSRoundConditionalGains`.
-/

theorem _root_.solution
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    ∃ regretGain informationGain : BanditHistory k t.1 → ℝ,
      Integrable regretGain nu ∧
      Integrable (fun h ↦ regretGain h ^ 2) nu ∧
      Integrable informationGain nu ∧
      (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
          ∂bayesianAdversarialMeasure Q pi n le_rfl) = ∫ h, regretGain h ∂nu ∧
      (∀ᵐ h ∂nu, regretGain h ^ 2 ≤ ((k : ℝ) / 2) * informationGain h) ∧
      (∫ h, informationGain h ∂nu) ≤
        bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
          bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  dsimp only
  refine ⟨bayesianTSRoundConditionalRegretGain Q pi t,
    bayesianTSRoundConditionalInformationGain Q pi t, ?_⟩
  obtain ⟨hr, hrsq, hi, hpoint⟩ :=
    bayesian_ts_conditional_gains_information_ratio Q hQ hpi t
  obtain ⟨hregret, hinfo⟩ := bayesian_ts_conditional_gains_accounting Q hQ t
  exact ⟨hr, hrsq, hi, hregret, hpoint, hinfo⟩

end BanditAlgorithm
