-- Prove2me | solution 1 for tangent_sampling_talagrand_increment_bound_from_coordinate_bound_min
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:03:00.059891+00:00
-- url     : https://prove2.me/submissions/8ebf30f8-87be-4213-bfa2-a1ec6ad4e479

import Definitions.Def_matrix_completion_talagrand
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open MatrixCompletion
open scoped BigOperators

namespace MatrixCompletion

/-- Cauchy–Schwarz for the matrix Frobenius inner product:
`|⟨X,Y⟩| ≤ ‖X‖_F · ‖Y‖_F`. -/
lemma abs_matrixInner_le {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  -- flatten the double sum into one sum over the product index
  have hCS :
      (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    -- flatten ∑_i ∑_j  to  ∑ over the product index
    have flat : ∀ (F : Fin n1 → Fin n2 → ℝ),
        (∑ i : Fin n1, ∑ j : Fin n2, F i j) =
          ∑ p : Fin n1 × Fin n2, F p.1 p.2 := by
      intro F
      rw [← Finset.sum_product']
      rfl
    have key :
        (∑ p : Fin n1 × Fin n2, X p.1 p.2 * Y p.1 p.2) ^ 2 ≤
          (∑ p : Fin n1 × Fin n2, (X p.1 p.2) ^ 2) *
            (∑ p : Fin n1 × Fin n2, (Y p.1 p.2) ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun p : Fin n1 × Fin n2 => X p.1 p.2)
        (fun p : Fin n1 × Fin n2 => Y p.1 p.2)
    rw [matrixInner, frobeniusNormSq, frobeniusNormSq, flat, flat, flat]
    exact key
  -- take sqrt
  have hX : (0:ℝ) ≤ frobeniusNormSq X := by
    unfold frobeniusNormSq; positivity
  have hY : (0:ℝ) ≤ frobeniusNormSq Y := by
    unfold frobeniusNormSq; positivity
  have h1 : |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    exact hCS
  calc |matrixInner X Y| ≤ Real.sqrt (frobeniusNormSq X * frobeniusNormSq Y) := h1
    _ = frobeniusNorm X * frobeniusNorm Y := by
        rw [Real.sqrt_mul hX]; rfl

/-- `n₁ * n₂ / min n₁ n₂ = max n₁ n₂` (as reals), for positive dims. -/
lemma natMul_div_min_eq_max (n1 n2 : ℕ) (h1 : 0 < n1) (h2 : 0 < n2) :
    ((n1 : ℝ) * (n2 : ℝ)) / (min (n1 : ℝ) (n2 : ℝ)) = max (n1 : ℝ) (n2 : ℝ) := by
  have c1 : (n1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have c2 : (n2 : ℝ) ≠ 0 := by exact_mod_cast h2.ne'
  rcases le_total (n1 : ℝ) (n2 : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right h]
    field_simp
  · rw [min_eq_right h, max_eq_left h]
    field_simp

end MatrixCompletion

open MatrixCompletion

/-- Dimension-correct (`min`-radius) increment feed: from the **achievable**
coordinate Frobenius bound `‖P_T(e_i e_j^*)‖_F² ≤ 2μ₀r/min(n₁,n₂)` (Candès–Recht
eq. (4.8)) we obtain the Talagrand increment bound `B = 2μ₀·max(n₁,n₂)·r/m`. -/
theorem solution :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → 0 < m → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandIncrementBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  intro n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hmle hμ hcoord
  intro X1 X2 hX1 hX2 i j
  set P := tangentProjection S (coordinateMatrix i j) with hP
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hpdef
  -- positivity facts
  have hn1R : (0:ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < n₂ := by exact_mod_cast hn2
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hprod : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := mul_pos hn1R hn2R
  have hp_pos : 0 < p := by rw [hpdef]; positivity
  -- coefficient = p⁻¹ * ⟨X1,P⟩ * ⟨P,X2⟩
  unfold tangentSamplingTalagrandCoefficient
  rw [← hP]
  -- |p⁻¹ * a * b| = p⁻¹ * |a| * |b|
  have hpinv_nonneg : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp_pos)
  rw [abs_mul, abs_mul, abs_of_nonneg hpinv_nonneg]
  -- bound the two inner products
  have hnormP_nonneg : 0 ≤ frobeniusNorm P := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hX1norm : frobeniusNorm X1 ≤ 1 := hX1
  have hX2norm : frobeniusNorm X2 ≤ 1 := hX2
  have hA : |matrixInner X1 P| ≤ frobeniusNorm P := by
    calc |matrixInner X1 P| ≤ frobeniusNorm X1 * frobeniusNorm P :=
            abs_matrixInner_le X1 P
      _ ≤ 1 * frobeniusNorm P := by
            apply mul_le_mul_of_nonneg_right hX1norm hnormP_nonneg
      _ = frobeniusNorm P := one_mul _
  have hB : |matrixInner P X2| ≤ frobeniusNorm P := by
    calc |matrixInner P X2| ≤ frobeniusNorm P * frobeniusNorm X2 :=
            abs_matrixInner_le P X2
      _ ≤ frobeniusNorm P * 1 := by
            apply mul_le_mul_of_nonneg_left hX2norm hnormP_nonneg
      _ = frobeniusNorm P := mul_one _
  -- |⟨X1,P⟩| * |⟨P,X2⟩| ≤ ‖P‖²
  have hsq : |matrixInner X1 P| * |matrixInner P X2| ≤ frobeniusNorm P ^ 2 := by
    have := mul_le_mul hA hB (abs_nonneg _) hnormP_nonneg
    calc |matrixInner X1 P| * |matrixInner P X2|
          ≤ frobeniusNorm P * frobeniusNorm P := this
      _ = frobeniusNorm P ^ 2 := by ring
  -- ‖P‖² ≤ 2μ₀r/min
  have hPsq : frobeniusNorm P ^ 2 ≤ 2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ) := by
    have := hcoord i j
    rw [← hP] at this
    exact this
  -- combine: p⁻¹ * (|a| * |b|) ≤ p⁻¹ * ‖P‖² ≤ p⁻¹ * (2μ₀r/min)
  have step1 : p⁻¹ * |matrixInner X1 P| * |matrixInner P X2|
      ≤ p⁻¹ * (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hpinv_nonneg
    exact le_trans hsq hPsq
  -- now show p⁻¹ * (2μ₀r/min) = 2μ₀·max·r/m
  have hmin_pos : (0:ℝ) < min (n₁ : ℝ) (n₂ : ℝ) := lt_min hn1R hn2R
  have hmax_cast : ((max n₁ n₂ : ℕ) : ℝ) = max (n₁ : ℝ) (n₂ : ℝ) := by
    push_cast; rfl
  have heq : p⁻¹ * (2 * μ₀ * (r : ℝ) / (min (n₁:ℝ) (n₂:ℝ)))
      = 2 * μ₀ * ((max n₁ n₂ : ℕ) : ℝ) * (r : ℝ) / (m : ℝ) := by
    rw [hpdef, inv_div, hmax_cast]
    have hmm := natMul_div_min_eq_max n₁ n₂ hn1 hn2
    have hmin_ne : min (n₁:ℝ) (n₂:ℝ) ≠ 0 := ne_of_gt hmin_pos
    have hm_ne : (m:ℝ) ≠ 0 := ne_of_gt hmR
    field_simp
    -- after clearing denominators, use hmm (as n₁n₂ = max * min)
    have hmm' : (n₁:ℝ) * (n₂:ℝ) = max (n₁:ℝ) (n₂:ℝ) * min (n₁:ℝ) (n₂:ℝ) := by
      rw [← hmm]; field_simp
    nlinarith [hmm', hmin_pos, hmR]
  rw [← heq]
  exact step1

