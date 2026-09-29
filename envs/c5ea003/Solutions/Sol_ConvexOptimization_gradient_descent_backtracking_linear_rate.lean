-- Prove2me | solution 1 for ConvexOptimization.gradient_descent_backtracking_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T15:09:32.21027+00:00
-- url     : https://prove2.me/submissions/f1f78272-f13a-48e0-8cd4-98ee70129e36

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Theorems.Thm_ConvexOptimization_strong_convexity_quadratic_lower_bound

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

open ConvexOptimization in
theorem solution {n : ℕ} (m M α β : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hα0 : 0 < α) (hα : α < 1 / 2)
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y : EuclideanSpace ℝ (Fin n),
      f y ≤ f x + ⟪g x, y - x⟫ + M / 2 * ‖y - x‖ ^ 2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k, ∃ t : ℝ,
      IsBacktrackingStep f g α β (x k) (-g (x k)) t ∧
      x (k + 1) = x k - t • g (x k)) :
    ∀ k, f (x k) - f xstar ≤
      (1 - min (2 * m * α) (2 * β * α * m / M)) ^ k * (f (x 0) - f xstar) := by
  have hM : (0 : ℝ) < M := lt_of_lt_of_le hm hmM
  set c : ℝ := min (2 * m * α) (2 * β * α * m / M) with hcdef
  -- The contraction factor is genuinely in `[0, 1)`.
  have hclt1 : c < 1 := by
    have h2α : 2 * α < 1 := by linarith
    have hbm : 0 < β * m := mul_pos hβ0 hm
    have hs1 : 2 * α * (β * m) < 1 * (β * m) := mul_lt_mul_of_pos_right h2α hbm
    have hs2 : β * m < m := by nlinarith
    have hs3 : 2 * β * α * m < M := by linarith
    have : 2 * β * α * m / M < 1 := (div_lt_one hM).mpr hs3
    exact lt_of_le_of_lt (min_le_right _ _) this
  have hrate : (0 : ℝ) ≤ 1 - c := by linarith
  have hsub : ∀ z, f z - f xstar ≤ ‖g z‖ ^ 2 / (2 * m) :=
    fun z => ConvexOptimization.strong_convexity_quadratic_lower_bound m hm f g hg hsc xstar hstar z
  have hmin : ∀ z, f xstar ≤ f z := fun z => isMinOn_iff.mp hstar z (Set.mem_univ z)
  -- Quadratic smoothness makes the Armijo condition hold for every step `s ≤ 2(1-α)/M`.
  have harm : ∀ (z : EuclideanSpace ℝ (Fin n)) (s : ℝ), 0 < s → s ≤ 2 * (1 - α) / M →
      f (z + s • (-g z)) ≤ f z + α * s * ⟪g z, -g z⟫ := by
    intro z s hs hsle
    have h2 := hsm z (z + s • (-g z))
    rw [show (z + s • (-g z)) - z = s • (-g z) from by abel] at h2
    rw [real_inner_smul_right, inner_neg_right, real_inner_self_eq_norm_sq,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs, norm_neg, mul_pow] at h2
    rw [inner_neg_right, real_inner_self_eq_norm_sq]
    have hMs2 : M * s / 2 - 1 + α ≤ 0 := by
      rw [le_div_iff₀ hM] at hsle
      linarith
    have hkey : ‖g z‖ ^ 2 * (M / 2 * s ^ 2 - s + α * s) ≤ 0 := by
      have hfac : M / 2 * s ^ 2 - s + α * s = s * (M * s / 2 - 1 + α) := by ring
      rw [hfac]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
        (mul_nonpos_of_nonneg_of_nonpos hs.le hMs2)
    nlinarith [h2, hkey]
  -- Hence backtracking returns a step of size at least `min 1 (β/M)`.
  have ht : ∀ k, ∃ t : ℝ, 0 < t ∧ min 1 (β / M) ≤ t ∧
      f (x (k + 1)) ≤ f (x k) - α * t * ‖g (x k)‖ ^ 2 := by
    intro k
    obtain ⟨t, ⟨⟨j, hj⟩, harmijo, hmax⟩, hxk⟩ := hstep k
    have htpos : 0 < t := by rw [hj]; positivity
    refine ⟨t, htpos, ?_, ?_⟩
    · rcases hmax with h1 | h2
      · rw [h1]; exact min_le_left _ _
      · have hs : 0 < t / β := div_pos htpos hβ0
        have hgt : ¬ (t / β ≤ 2 * (1 - α) / M) := fun hle => h2 (harm (x k) (t / β) hs hle)
        push_neg at hgt
        have hgt2 : 2 * (1 - α) / M * (β * M) < t / β * (β * M) :=
          mul_lt_mul_of_pos_right hgt (by positivity)
        have e1 : 2 * (1 - α) / M * (β * M) = 2 * (1 - α) * β := by field_simp
        have e2 : t / β * (β * M) = t * M := by field_simp
        rw [e1, e2] at hgt2
        have hβlt : β < t * M := by
          nlinarith [mul_pos (show (0 : ℝ) < 1 - 2 * α by linarith) hβ0]
        have hdiv : β / M < t := by rw [div_lt_iff₀ hM]; exact hβlt
        exact le_trans (min_le_right _ _) hdiv.le
    · rw [hxk]
      rw [show x k + t • (-g (x k)) = x k - t • g (x k) from by module,
        inner_neg_right, real_inner_self_eq_norm_sq] at harmijo
      linarith
  -- One backtracking step contracts the suboptimality by the factor `1 - c`.
  have key : ∀ k, f (x (k + 1)) - f xstar ≤ (1 - c) * (f (x k) - f xstar) := by
    intro k
    obtain ⟨t, htpos, htmin, hdec⟩ := ht k
    have hnn : 0 ≤ f (x k) - f xstar := by linarith [hmin (x k)]
    have hgnorm : 2 * m * (f (x k) - f xstar) ≤ ‖g (x k)‖ ^ 2 := by
      have hs := hsub (x k)
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * m)] at hs
      linarith
    have h1 : α * t * (2 * m * (f (x k) - f xstar)) ≤ α * t * ‖g (x k)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hgnorm (by positivity)
    have hct : c ≤ 2 * m * α * t := by
      have h0 : (0 : ℝ) ≤ 2 * m * α := by positivity
      have hs1 : 2 * m * α * min 1 (β / M) ≤ 2 * m * α * t :=
        mul_le_mul_of_nonneg_left htmin h0
      have hs2 : c ≤ 2 * m * α * min 1 (β / M) := by
        rcases min_cases (1 : ℝ) (β / M) with ⟨he, _⟩ | ⟨he, _⟩
        · rw [he, mul_one]; exact min_le_left _ _
        · rw [he, show 2 * m * α * (β / M) = 2 * β * α * m / M from by field_simp]
          exact min_le_right _ _
      linarith
    have h2 : c * (f (x k) - f xstar) ≤ 2 * m * α * t * (f (x k) - f xstar) :=
      mul_le_mul_of_nonneg_right hct hnn
    nlinarith [hdec, h1, h2]
  -- Iterate the contraction.
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (x (k + 1)) - f xstar
        ≤ (1 - c) * (f (x k) - f xstar) := key k
      _ ≤ (1 - c) * ((1 - c) ^ k * (f (x 0) - f xstar)) :=
          mul_le_mul_of_nonneg_left ih hrate
      _ = (1 - c) ^ (k + 1) * (f (x 0) - f xstar) := by ring
