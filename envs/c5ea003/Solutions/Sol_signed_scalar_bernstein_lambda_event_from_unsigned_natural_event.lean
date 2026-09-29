-- Prove2me | solution 1 for signed_scalar_bernstein_lambda_event_from_unsigned_natural_event
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T06:44:17.743469+00:00
-- url     : https://prove2.me/submissions/8b8abf74-a4fa-4a70-b2c0-fd9c643cacc0

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

/-- Pointwise deterministic transfer from the unsigned natural-scale scalar
Bernstein event to the signed `λ^{-1}` event. -/
theorem solution
    (Cnatural Ccompat : ℝ) :
    0 < Cnatural → 0 < Ccompat →
    ∃ Cpoint : ℝ, 0 < Cpoint ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ sign : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        |sign| *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2) ≤
          Ccompat * Real.rpow lam (-1) →
        ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
          (B : Matrix (Fin n₁) (Fin n₂) ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            sign *
              matrixEntrySum
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        |matrixEntrySum
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)| ≤
          Cnatural *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
              Real.rpow
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
                ((3 : ℝ) / 2) →
        |Coeff Omega| ≤ Cpoint * Real.rpow lam (-1) := by
  intro hCnatural hCcompat
  refine ⟨Cnatural * Ccompat, mul_pos hCnatural hCcompat, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ sign hn₁ hn₂ hr hm hμ₀ hcompat Coeff B hCoeff
    Omega hunsigned
  calc
    |Coeff Omega| =
        |sign| *
          |matrixEntrySum
            (centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)| := by
          rw [hCoeff Omega, abs_mul]
    _ ≤ |sign| *
        (Cnatural *
          Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2)) := by
          exact mul_le_mul_of_nonneg_left hunsigned (abs_nonneg sign)
    _ = Cnatural *
        (|sign| *
          Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow
              ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
              ((3 : ℝ) / 2)) := by ring
    _ ≤ Cnatural * (Ccompat * Real.rpow lam (-1)) := by
          exact mul_le_mul_of_nonneg_left hcompat (le_of_lt hCnatural)
    _ = (Cnatural * Ccompat) * Real.rpow lam (-1) := by ring
