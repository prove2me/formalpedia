-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-24T18:39:27.405639+00:00
-- url     : https://prove2.me/submissions/0ecfe497-39a7-407e-8655-0145de913b43

import Definitions.Def_linear_neumann_offdiag_bernstein
import Theorems.Thm_entry_sup_norm_sign_matrix_bound_from_a1
import Theorems.Thm_tangent_coordinate_frobenius_bound_from_a0_min_dim
import Theorems.Thm_tangent_coordinate_frobenius_sq_bound_implies_radius_bound
import Theorems.Thm_tangent_coordinate_kernel_symm

open MatrixCompletion
open scoped Classical BigOperators

namespace ProveLinearOffdiagBaseFrobeniusMin

theorem entry_le_sup {n₁ n₂ : Nat} (X : RealMatrix n₁ n₂) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  rw [entrySupNorm]
  refine le_trans ?_ (le_ciSup (f := fun i => ⨆ j : Fin n₂, |X i j|)
    (Finite.bddAbove_range _) i)
  exact le_ciSup (f := fun j => |X i j|) (Finite.bddAbove_range _) j

theorem matrix_inner_coordinate
    {n₁ n₂ : Nat} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (a : Fin n₁) (b : Fin n₂) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  classical
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hb
      simp at hb
  · intro x _ hx
    rw [Finset.sum_eq_zero]
    intro y _
    simp [hx]
  · intro ha
    simp at ha

theorem frobeniusNorm_le_mul_of_entrywise_abs_le
    {n₁ n₂ : Nat} (X Y : RealMatrix n₁ n₂) (c : ℝ)
    (hc : 0 ≤ c)
    (hentry : ∀ i j, |X i j| ≤ c * |Y i j|) :
    frobeniusNorm X ≤ c * frobeniusNorm Y := by
  have hsq_entry : ∀ i j, X i j ^ 2 ≤ c ^ 2 * Y i j ^ 2 := by
    intro i j
    have hnonneg : 0 ≤ c * |Y i j| := mul_nonneg hc (abs_nonneg _)
    have habs : |X i j| ≤ |c * (|Y i j|)| := by
      simpa [abs_of_nonneg hnonneg] using hentry i j
    have hsq := sq_le_sq.mpr habs
    calc
      X i j ^ 2 ≤ (c * |Y i j|) ^ 2 := hsq
      _ = c ^ 2 * Y i j ^ 2 := by
        rw [mul_pow, sq_abs]
  have hsum : frobeniusNormSq X ≤ c ^ 2 * frobeniusNormSq Y := by
    unfold frobeniusNormSq
    calc
      (∑ i : Fin n₁, ∑ j : Fin n₂, X i j ^ 2)
          ≤ ∑ i : Fin n₁, ∑ j : Fin n₂, c ^ 2 * Y i j ^ 2 := by
            exact Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ => hsq_entry i j))
      _ = c ^ 2 * (∑ i : Fin n₁, ∑ j : Fin n₂, Y i j ^ 2) := by
            simp [Finset.mul_sum]
  calc
    frobeniusNorm X = Real.sqrt (frobeniusNormSq X) := rfl
    _ ≤ Real.sqrt (c ^ 2 * frobeniusNormSq Y) := Real.sqrt_le_sqrt hsum
    _ = c * frobeniusNorm Y := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]
      rfl

end ProveLinearOffdiagBaseFrobeniusMin

open ProveLinearOffdiagBaseFrobeniusMin

theorem solution :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt
                  (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  obtain ⟨Ccoord, hCcoord, hcoord⟩ := tangent_coordinate_frobenius_bound_from_a0_min_dim
  refine ⟨Real.sqrt Ccoord, Real.sqrt_pos.2 hCcoord, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
  have hsign_sup :
      entrySupNorm (signMatrix S) ≤
        μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
    entry_sup_norm_sign_matrix_bound_from_a1 hn₁ hn₂ μ₁ S hA1
  have hsign_nonneg :
      0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by
    positivity
  let Tcoord : RealMatrix n₁ n₂ := tangentProjection S (coordinateMatrix w.1 w.2)
  have hentry :
      ∀ i j,
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j| ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) * |Tcoord i j| := by
    intro i j
    by_cases hdiag : (i, j) = w
    · calc
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j| = 0 := by
          simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag]
        _ ≤
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              |Tcoord i j| := by
            exact mul_nonneg hsign_nonneg (abs_nonneg _)
    · have hsign_entry :
          |signMatrix S i j| ≤
            μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) :=
        le_trans (entry_le_sup (signMatrix S) i j) hsign_sup
      have hkernel_eq :
          tangentCoordinateKernel S i j w.1 w.2 = Tcoord i j := by
        rw [tangent_coordinate_kernel_symm]
        rw [tangentCoordinateKernel, matrix_inner_coordinate]
      calc
        |linearNeumannOffDiagonalCoefficientBaseMatrix S w i j|
            = |signMatrix S i j| * |Tcoord i j| := by
              simp [linearNeumannOffDiagonalCoefficientBaseMatrix, hdiag, abs_mul, hkernel_eq]
        _ ≤
            (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              |Tcoord i j| := by
              exact mul_le_mul_of_nonneg_right hsign_entry (abs_nonneg _)
  have hbase_le :
      frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          frobeniusNorm Tcoord :=
    frobeniusNorm_le_mul_of_entrywise_abs_le
      (linearNeumannOffDiagonalCoefficientBaseMatrix S w) Tcoord
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) hsign_nonneg hentry
  have hradiusSq_nonneg :
      0 ≤ Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
    positivity
  have hcoord_bound :
      TangentCoordinateFrobeniusBound S
        (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) :=
    hcoord n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0
  have hTcoord_le :
      frobeniusNorm Tcoord ≤
        Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    exact tangent_coordinate_frobenius_sq_bound_implies_radius_bound
      S (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)))
      hradiusSq_nonneg hcoord_bound w.1 w.2
  have hmul :
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          frobeniusNorm Tcoord ≤
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    exact mul_le_mul_of_nonneg_left hTcoord_le hsign_nonneg
  have hsqrt_split :
      Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) =
        Real.sqrt Ccoord *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
    have hrest : 0 ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
      positivity
    have hrewrite :
        Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂)) =
          Ccoord * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
      ring
    rw [hrewrite, Real.sqrt_mul (le_of_lt hCcoord)]
  calc
    frobeniusNorm (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
        ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            frobeniusNorm Tcoord := hbase_le
    _ ≤
          (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            Real.sqrt (Ccoord * μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := hmul
    _ =
          Real.sqrt Ccoord * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
        rw [hsqrt_split]
        ring
