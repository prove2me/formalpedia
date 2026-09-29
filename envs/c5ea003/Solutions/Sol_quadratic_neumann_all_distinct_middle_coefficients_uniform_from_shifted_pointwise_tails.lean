-- Prove2me | solution 1 for quadratic_neumann_all_distinct_middle_coefficients_uniform_from_shifted_pointwise_tails
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T23:21:44.750288+00:00
-- url     : https://prove2.me/submissions/0804d3dd-b7fb-4091-a80c-099193a7cbec

import Definitions.Def_matrix_completion_neumann
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Theorems.Thm_sample_ratio_between_zero_and_one

open MatrixCompletion

/-!
Source: Candes-Recht 2008, PDF p. 29, the union-bound step after equation
(6.17), and PDF p. 30, equation (6.20), where the all-distinct quadratic
Neumann term is reduced to coordinate-indexed coefficient events.  This repairs
the old no-loss uniformization node by explicitly paying the coordinate
cardinality factor with pointwise tails at exponent `β + 2`.
-/

theorem solution
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ccond ccond : ℝ, 0 < Ccond ∧ 0 < ccond ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Cinner : ℝ, 0 < Cinner →
        ∀ Omega3 : Finset (Fin n₁ × Fin n₂),
        QuadraticAllDistinctInnerCoefficientBound Omega3 S
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (Cinner * Real.rpow lam (-((1 : ℝ) / 2))) →
        (∀ w1 : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                  (Cpoint * Cinner) * Real.rpow lam (-1)) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                ((Ccond * Cinner) * Real.rpow lam (-1))) ≥
          1 - ccond * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  rcases bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cpoint cpoint hCpoint hcpoint with
    ⟨Ccond, ccond, hCcond, hccond, hUniform⟩
  refine ⟨Ccond, ccond, hCcond, hccond, ?_⟩
  intro β lam hβ _hlam n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower
    Cinner _hCinner Omega3 _hInner hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  let scale : ℝ := Cinner * Real.rpow lam (-1)
  have hPointwise' :
      ∀ w1 : Fin n₁ × Fin n₂,
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              |quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1| ≤
                Cpoint * scale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w1
    simpa [scale, mul_assoc] using hPointwise w1
  have h :=
    hUniform β ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) scale hβ
      hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
      (fun w1 Omega2 =>
        quadraticAllDistinctMiddleCoefficient Omega2 Omega3 S
          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w1)
      hPointwise'
  simpa [QuadraticAllDistinctMiddleCoefficientBound, scale, mul_assoc] using h
