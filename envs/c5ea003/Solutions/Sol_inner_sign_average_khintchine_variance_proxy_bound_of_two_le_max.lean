-- Prove2me | solution 1 for inner_sign_average_khintchine_variance_proxy_bound_of_two_le_max
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-26T00:57:04.162993+00:00
-- url     : https://prove2.me/submissions/660eceea-cffe-4879-8ddf-6ea81c74b538

import Theorems.Thm_sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.EquivFin

open Matrix MatrixCompletion
open scoped Classical BigOperators Matrix Matrix.Norms.L2Operator

private theorem frobenius_vector_dot_eq_sq {n₁ n₂ : Nat}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    (fun e : Fin n₁ × Fin n₂ => X e.1 e.2) ⬝ᵥ
        (fun e : Fin n₁ × Fin n₂ => X e.1 e.2)
      = frobeniusNormSq X := by
  unfold frobeniusNormSq
  rw [dotProduct]
  rw [Fintype.sum_prod_type]
  simp [pow_two]

private theorem vector_dot_le_sq_of_frobenius_le {n₁ n₂ : Nat}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) {R : ℝ}
    (hR : 0 ≤ R) (hX : frobeniusNorm X ≤ R) :
    (fun e : Fin n₁ × Fin n₂ => X e.1 e.2) ⬝ᵥ
        (fun e : Fin n₁ × Fin n₂ => X e.1 e.2)
      ≤ R ^ 2 := by
  rw [frobenius_vector_dot_eq_sq X]
  have hnonneg : 0 ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq
    positivity
  have hsqrt_sq : frobeniusNorm X ^ 2 = frobeniusNormSq X := by
    unfold frobeniusNorm
    exact Real.sq_sqrt hnonneg
  have hsquare_le : frobeniusNorm X ^ 2 ≤ R ^ 2 := by
    have hfrob_nonneg : 0 ≤ frobeniusNorm X := by
      unfold frobeniusNorm
      exact Real.sqrt_nonneg _
    exact (sq_le_sq₀ hfrob_nonneg hR).2 hX
  simpa [hsqrt_sq] using hsquare_le

theorem solution :
    ∃ Csym0 : ℝ, 0 < Csym0 ∧
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (S : SVD M r) (R : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        2 ≤ max n₁ n₂ →
        0 ≤ R →
        (∀ i : Fin n₁, ∀ j : Fin n₂,
          frobeniusNorm (tangentProjection S (coordinateMatrix i j)) ≤ R) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂)),
        (∑ Es : Finset (Fin n₁ × Fin n₂),
            ((1:ℝ)/2) ^ (Fintype.card (Fin n₁ × Fin n₂)) *
              ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                (∑ ab : Fin n₁ × Fin n₂,
                  (((if ab ∈ Es then (1:ℝ) else -1) *
                      (if ab ∈ Omega then (1:ℝ) else 0)) •
                    Matrix.vecMulVec
                      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                      (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖)
          ≤ Csym0 *
              (Real.sqrt (Real.log (↑(max n₁ n₂))) * R) *
              Real.sqrt
                ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
                  (∑ ab : Fin n₁ × Fin n₂,
                    (if ab ∈ Omega then (1:ℝ) else 0) •
                      Matrix.vecMulVec
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                        (fun e : Fin n₁ × Fin n₂ => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2))))‖ := by
  rcases sampled_rank_one_rademacher_average_bound_from_radius_and_gram_opnorm with
    ⟨Csym0, hCsym0_pos, hCsym0⟩
  refine ⟨Csym0, hCsym0_pos, ?_⟩
  intro n₁ n₂ r m M S R hn₁ hn₂ _hr _hm hmax hR hRadius Omega
  let α := Fin n₁ × Fin n₂
  let y : α → α → ℝ :=
    fun ab e => tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2
  have hcard_pos : 0 < Fintype.card α := by
    dsimp [α]
    rw [Fintype.card_prod]
    exact Nat.mul_pos (by simpa using hn₁) (by simpa using hn₂)
  have hcard_le : Fintype.card α ≤ max n₁ n₂ * max n₁ n₂ := by
    dsimp [α]
    simpa [Fintype.card_prod] using
      Nat.mul_le_mul (Nat.le_max_left n₁ n₂) (Nat.le_max_right n₁ n₂)
  have hRadiusDot : ∀ c : α, (y c ⬝ᵥ y c) ≤ R ^ 2 := by
    intro ab
    exact vector_dot_le_sq_of_frobenius_le
      (tangentProjection S (coordinateMatrix ab.1 ab.2))
      hR (hRadius ab.1 ab.2)
  have hmain :=
    hCsym0 (α := α) (N := max n₁ n₂)
      hcard_pos hmax hcard_le y R hR hRadiusDot Omega
  simpa [α, y] using hmain
