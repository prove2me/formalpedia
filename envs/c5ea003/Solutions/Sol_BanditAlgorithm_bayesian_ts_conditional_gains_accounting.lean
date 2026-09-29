-- Prove2me | solution 1 for BanditAlgorithm.bayesian_ts_conditional_gains_accounting
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T01:49:08.326942+00:00
-- url     : https://prove2.me/submissions/bc3685e2-ef5c-43c8-b7f4-89601fd52f39

import Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_regret_gain_integral
import Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_information_gain_chain_rule

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-! Source: Lattimore--Szepesvari, *Bandit Algorithms* (2020), Lemma 36.7,
printed p. 470 / free PDF p. 479.  This bridge separates the tower-property
regret identity from the KL chain-rule information identity. -/

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
      ∫ h, bayesianTSRoundConditionalRegretGain Q pi t h ∂nu ∧
    (∫ h, bayesianTSRoundConditionalInformationGain Q pi t h ∂nu) ≤
      bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
        bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  exact ⟨bayesian_ts_conditional_regret_gain_integral Q hQ t,
    bayesian_ts_conditional_information_gain_chain_rule Q t⟩

end BanditAlgorithm
