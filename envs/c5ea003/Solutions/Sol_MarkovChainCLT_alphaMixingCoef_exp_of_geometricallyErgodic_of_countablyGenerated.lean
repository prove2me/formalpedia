-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_exp_of_geometricallyErgodic_of_countablyGenerated
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-07T01:28:00.451936+00:00
-- url     : https://prove2.me/submissions/a6b5bb8b-6032-4f9e-8513-dc882fcc8885

import Theorems.Thm_MarkovChainCLT_geoDriftCondition_of_geometricallyErgodic
import Theorems.Thm_MarkovChainCLT_ergodicWithRate_of_geoDriftCondition
import Theorems.Thm_MarkovChainCLT_integrable_of_geoDriftCondition
import Theorems.Thm_MarkovChainCLT_alpha_mixing_le_tv_rate
import Theorems.Thm_MarkovChainCLT_alphaMixingCoef_le_quarter

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution
    {X : Type*} [MeasurableSpace X] [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (hgeo : GeometricallyErgodic P π) :
    ∃ c a : ℝ, 0 ≤ c ∧ 0 ≤ a ∧ a < 1 ∧
      ∀ n : ℕ, alphaMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n ≤ c * a ^ n := by
  -- (1) Meyn–Tweedie 15.0.1, (i) ⇒ (iii): a geometric drift function `V ≥ 1` towards a small set
  obtain ⟨V, hV, hV1, C, hC, hsmall, d, b, hd, hdrift⟩ :=
    geoDriftCondition_of_geometricallyErgodic P π hP hgeo
  -- (2) Meyn–Tweedie 15.0.1, (iii) ⇒ (i): a total-variation rate with constant `R · V`
  obtain ⟨R, ρ, hR0, hρ0, hρ1, hrate⟩ :=
    ergodicWithRate_of_geoDriftCondition P π hP V hV hV1 C hC hsmall d b hd hdrift
  -- (3) Meyn–Tweedie 14.3.7: `E_π V < ∞`
  have hVint : Integrable V π :=
    integrable_of_geoDriftCondition P π hP V hV hV1 C hC hsmall d b hd hdrift
  have hM0 : ∀ x, 0 ≤ R * V x := fun x => mul_nonneg hR0 (zero_le_one.trans (hV1 x))
  have hMint : Integrable (fun x => R * V x) π := hVint.const_mul R
  -- (4) Jones Theorem 2(ii): `α(n) ≤ ρⁿ E_π (R V)` for `n ≥ 1`
  have hmix := alpha_mixing_le_tv_rate P π hP (fun x => R * V x) hM0 hMint (fun n => ρ ^ n)
    (fun n => pow_nonneg hρ0 n) hrate
  have hInt0 : 0 ≤ ∫ x, R * V x ∂π := integral_nonneg hM0
  refine ⟨(∫ x, R * V x ∂π) + 1 / 4, ρ, by linarith, hρ0, hρ1, ?_⟩
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- lag 0: a mixing coefficient of a probability process is at most 1/4
    have h := alphaMixingCoef_le_quarter (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
      (fun i => measurable_pi_apply i) 0
    simpa using h.trans (by linarith)
  · have h := hmix n hn
    have hρn : 0 ≤ ρ ^ n := pow_nonneg hρ0 n
    nlinarith
