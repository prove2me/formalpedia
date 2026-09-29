-- Prove2me | solution 1 for scalar_centered_sampling_bernstein_lambda_half_tail_from_quadratic_base_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-14T05:25:35.491796+00:00
-- url     : https://prove2.me/submissions/8858004d-b791-4f58-9ae8-a86945471be5

import Theorems.Thm_scalar_centered_sampling_bernstein_lambda_half_tail_from_quadratic_base_bounds
import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_quadratic_base_scalar_bernstein_lambda_half_scale_absorption
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-- Split the `λ^{-1/2}` scalar Bernstein estimate into raw Bernstein and the
Lemma 4.6 scale absorption. -/
theorem solution
    (Centry Cfro : ℝ) :
    0 < Centry → 0 < Cfro →
    ∃ Cpoint cpoint : ℝ, 0 < Cpoint ∧ 0 < cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤
          Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(max n₁ n₂))) ^ 2) →
        frobeniusNorm B ≤
          Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCentry hCfro
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  rcases quadratic_base_scalar_bernstein_lambda_half_scale_absorption
      Cbern Centry Cfro hCbern hCentry hCfro with
    ⟨Cpoint, hCpoint, hAbsorb⟩
  refine ⟨Cpoint, cbern, hCpoint, hcbern, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀
    hn₁ hn₂ hr hm hμ₀ hmLower Coeff B hRep hEntry hFrob
  let entryScale : ℝ :=
    Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(max n₁ n₂))) ^ 2)
  let frobScale : ℝ :=
    Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
      Real.rpow ((r : ℝ) / (↑(max n₁ n₂))) ((3 : ℝ) / 2)
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  have hp : 0 ≤ p ∧ p ≤ 1 := by
    exact sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm
  have hRawProb :=
    hBernstein β hβ n₁ n₂ m hn₁ hn₂ hm
      Coeff B entryScale frobScale hRep hEntry hFrob
  have hScale :
      Cbern *
          (Real.sqrt
              ((β * Real.log (↑(max n₁ n₂))) / p) *
            frobScale +
            ((β * Real.log (↑(max n₁ n₂))) / p) * entryScale) ≤
        Cpoint * Real.rpow lam (-((1 : ℝ) / 2)) := by
    exact hAbsorb β lam hβ hlam n₁ n₂ r m μ₀
      hn₁ hn₂ hr hm hμ₀ hmLower
  have hMono :
      bernoulliEventProb p
          (fun Omega =>
            |Coeff Omega| ≤
              Cbern *
                (Real.sqrt ((β * Real.log (↑(max n₁ n₂))) / p) *
                  frobScale +
                  ((β * Real.log (↑(max n₁ n₂))) / p) * entryScale)) ≤
        bernoulliEventProb p
          (fun Omega =>
            |Coeff Omega| ≤
              Cpoint * Real.rpow lam (-((1 : ℝ) / 2))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hOmega
    exact le_trans hOmega hScale
  exact le_trans hRawProb hMono

