-- Prove2me | solution 2 for ConvexOptimization.gradient_descent_backtracking_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-15T15:14:22.902378+00:00
-- url     : https://prove2.me/submissions/061d863e-84c7-4bdd-9ee0-b83dbb5c06bb

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Theorems.Thm_ConvexOptimization_strong_convexity_quadratic_lower_bound

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

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
      ConvexOptimization.IsBacktrackingStep f g α β (x k) (-g (x k)) t ∧
      x (k + 1) = x k - t • g (x k)) :
    ∀ k, f (x k) - f xstar ≤
      (1 - min (2 * m * α) (2 * β * α * m / M)) ^ k * (f (x 0) - f xstar) := by
  have hM : (0 : ℝ) < M := lt_of_lt_of_le hm hmM
  have hratio0 : (0 : ℝ) ≤ m / M := div_nonneg hm.le hM.le
  have hratio1 : m / M ≤ (1 : ℝ) := (div_le_one hM).2 hmM
  have hβratio1 : β * (m / M) ≤ (1 : ℝ) := by
    calc
      β * (m / M) ≤ 1 * (m / M) :=
        mul_le_mul_of_nonneg_right hβ1.le hratio0
      _ ≤ 1 := by simpa using hratio1
  have hsecond_lt : 2 * β * α * m / M < (1 : ℝ) := by
    have hle : 2 * β * α * m / M ≤ 2 * α := by
      calc
        2 * β * α * m / M = (2 * α) * (β * (m / M)) := by ring
        _ ≤ (2 * α) * 1 :=
          mul_le_mul_of_nonneg_left hβratio1 (by positivity)
        _ = 2 * α := by ring
    linarith
  have hrate : (0 : ℝ) ≤ 1 - min (2 * m * α) (2 * β * α * m / M) := by
    have hminlt : min (2 * m * α) (2 * β * α * m / M) < (1 : ℝ) :=
      lt_of_le_of_lt (min_le_right _ _) hsecond_lt
    linarith
  have hsub : ∀ z : EuclideanSpace ℝ (Fin n),
      f z - f xstar ≤ ‖g z‖ ^ 2 / (2 * m) :=
    fun z => ConvexOptimization.strong_convexity_quadratic_lower_bound
      m hm f g hg hsc xstar hstar z
  have key : ∀ k, f (x (k + 1)) - f xstar ≤
      (1 - min (2 * m * α) (2 * β * α * m / M)) * (f (x k) - f xstar) := by
    intro k
    obtain ⟨t, ht, hxnext⟩ := hstep k
    rcases ht with ⟨⟨j, htj⟩, harmijo, hmax⟩
    have ht0 : (0 : ℝ) < t := by rw [htj]; positivity
    have hstepLower : min 1 (β / M) ≤ t := by
      rcases hmax with ht_one | hfailed
      · rw [ht_one]
        exact min_le_left _ _
      · have hstrict : β / M < t := by
          by_contra hnot
          have ht_le : t ≤ β / M := le_of_not_gt hnot
          let s : ℝ := t / β
          have hs0 : (0 : ℝ) ≤ s := by
            dsimp [s]
            positivity
          have hs_le : s ≤ 1 / M := by
            dsimp [s]
            rw [div_le_iff₀ hβ0]
            convert ht_le using 1 <;> field_simp
          have hsM : s * M ≤ 1 := (le_div_iff₀ hM).mp hs_le
          have hsprod : 0 ≤ s * (1 - s * M) :=
            mul_nonneg hs0 (sub_nonneg.mpr hsM)
          have hquad : -s + M / 2 * s ^ 2 ≤ -α * s := by
            nlinarith
          have hsmooth := hsm (x k) (x k - s • g (x k))
          rw [show (x k - s • g (x k)) - x k = -(s • g (x k)) from by abel,
            inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
            norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow] at hsmooth
          have hquad_mul :
              (-s + M / 2 * s ^ 2) * ‖g (x k)‖ ^ 2 ≤
                (-α * s) * ‖g (x k)‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hquad (sq_nonneg _)
          have hprev :
              f (x k + s • (-g (x k))) ≤
                f (x k) + α * s * ⟪g (x k), -g (x k)⟫ := by
            rw [smul_neg, ← sub_eq_add_neg, inner_neg_right,
              real_inner_self_eq_norm_sq]
            nlinarith [hsmooth, hquad_mul]
          exact hfailed (by simpa [s] using hprev)
        exact le_of_lt (lt_of_le_of_lt (min_le_right _ _) hstrict)
    have hdec0 : f (x (k + 1)) ≤ f (x k) - α * t * ‖g (x k)‖ ^ 2 := by
      rw [hxnext]
      simpa [sub_eq_add_neg, smul_neg, inner_neg_right,
        real_inner_self_eq_norm_sq] using harmijo
    have hcoef : min α (β * α / M) ≤ α * t := by
      calc
        min α (β * α / M) = min (α * 1) (α * (β / M)) := by
          congr 1 <;> ring
        _ = α * min 1 (β / M) :=
          (mul_min_of_nonneg 1 (β / M) hα0.le).symm
        _ ≤ α * t := mul_le_mul_of_nonneg_left hstepLower hα0.le
    have hdec : f (x (k + 1)) ≤
        f (x k) - min α (β * α / M) * ‖g (x k)‖ ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖g (x k)‖)
      linarith
    have hR : min (2 * m * α) (2 * β * α * m / M) =
        2 * m * min α (β * α / M) := by
      calc
        min (2 * m * α) (2 * β * α * m / M) =
            min ((2 * m) * α) ((2 * m) * (β * α / M)) := by
          congr 1 <;> ring
        _ = 2 * m * min α (β * α / M) :=
          (mul_min_of_nonneg α (β * α / M)
            (show (0 : ℝ) ≤ 2 * m by positivity)).symm
    have hscaled := mul_le_mul_of_nonneg_left (hsub (x k))
      (show 0 ≤ 2 * m * min α (β * α / M) by positivity)
    have hgrad :
        min (2 * m * α) (2 * β * α * m / M) * (f (x k) - f xstar) ≤
          min α (β * α / M) * ‖g (x k)‖ ^ 2 := by
      rw [hR]
      calc
        2 * m * min α (β * α / M) * (f (x k) - f xstar)
            ≤ 2 * m * min α (β * α / M) *
                (‖g (x k)‖ ^ 2 / (2 * m)) := hscaled
        _ = min α (β * α / M) * ‖g (x k)‖ ^ 2 := by
          field_simp
    nlinarith [hdec, hgrad]
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      f (x (k + 1)) - f xstar
          ≤ (1 - min (2 * m * α) (2 * β * α * m / M)) *
              (f (x k) - f xstar) := key k
      _ ≤ (1 - min (2 * m * α) (2 * β * α * m / M)) *
              ((1 - min (2 * m * α) (2 * β * α * m / M)) ^ k *
                (f (x 0) - f xstar)) := mul_le_mul_of_nonneg_left ih hrate
      _ = (1 - min (2 * m * α) (2 * β * α * m / M)) ^ (k + 1) *
              (f (x 0) - f xstar) := by ring
