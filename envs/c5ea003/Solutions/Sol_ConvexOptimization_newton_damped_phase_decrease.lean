-- Prove2me | solution 1 for ConvexOptimization.newton_damped_phase_decrease
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T10:00:35.91903+00:00
-- url     : https://prove2.me/submissions/edcf8e7f-21e5-4cde-99ca-0a1149a91206

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep
import Theorems.Thm_ConvexOptimization_hessian_lower_bound_implies_strong_convexity

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

private theorem hessian_symmetric {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    ⟪H x u, v⟫ = ⟪u, H x v⟫ := by
  let D := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv.toContinuousLinearMap
  have hf' : ∀ y, HasFDerivAt f (D (g y)) y := by
    intro y
    simpa [D] using hg y
  have hf'' : HasFDerivAt (fun y => D (g y)) (D.comp (H x)) x :=
    D.hasFDerivAt.comp x (hH x)
  have hs := second_derivative_symmetric hf' hf'' u v
  simpa [D, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hs

private theorem smooth_upper_of_hessian_upper {n : ℕ} (M : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (x d : EuclideanSpace ℝ (Fin n)) :
    f (x + d) ≤ f x + ⟪g x, d⟫ + M / 2 * ‖d‖ ^ 2 := by
  have hneggrad : ∀ y, HasGradientAt (fun z => -f z) (-g y) y := by
    intro y
    rw [hasGradientAt_iff_hasFDerivAt]
    simpa using (hg y).hasFDerivAt.neg
  have hnegH : ∀ y, HasFDerivAt (fun z => -g z) (-H y) y := by
    intro y
    simpa using (hH y).neg
  have hnegbound : ∀ y v,
      (-M) * ‖v‖ ^ 2 ≤ ⟪(-H y) v, v⟫ := by
    intro y v
    simpa using neg_le_neg (hHM y v)
  have h := ConvexOptimization.hessian_lower_bound_implies_strong_convexity
    (-M) (fun z => -f z) (fun z => -g z) hneggrad
    (fun z => -H z) hnegH hnegbound x (x + d)
  simp [inner_neg_left] at h
  ring_nf at h ⊢
  linarith

theorem solution {n : ℕ} (m M L α β η : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hL : 0 < L)
    (hα0 : 0 < α) (hα : α < 1 / 2) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hη : η = min 1 (3 * (1 - 2 * α)) * m ^ 2 / L)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hHm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (hHM : ∀ x v, ⟪H x v, v⟫ ≤ M * ‖v‖ ^ 2)
    (hHL : ∀ x y, ‖H x - H y‖ ≤ L * ‖x - y‖)
    (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (hΔ : H x Δ = -g x) (hgx : η ≤ ‖g x‖)
    (ht : ConvexOptimization.IsBacktrackingStep f g α β x Δ t) :
    f (x + t • Δ) ≤ f x - α * β * η ^ 2 * m / M ^ 2 := by
  have hM : 0 < M := lt_of_lt_of_le hm hmM
  have hinner : ⟪g x, Δ⟫ = -⟪H x Δ, Δ⟫ := by
    have hg' : g x = -H x Δ := by
      simpa using (congrArg Neg.neg hΔ).symm
    rw [hg']
    simp
  have hA0 : 0 ≤ ⟪H x Δ, Δ⟫ := by
    exact (mul_nonneg (le_of_lt hm) (sq_nonneg ‖Δ‖)).trans (hHm x Δ)
  have harmijo_small (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ m / M) :
      f (x + s • Δ) ≤ f x + α * s * ⟪g x, Δ⟫ := by
    have hsmooth := smooth_upper_of_hessian_upper M f g hg H hH hHM x (s • Δ)
    have hMs : M * s ≤ m := by simpa [mul_comm] using (le_div_iff₀ hM).mp hs
    have hquad : M / 2 * s ^ 2 * ‖Δ‖ ^ 2 ≤ (1 - α) * s * ⟪H x Δ, Δ⟫ := by
      calc
        M / 2 * s ^ 2 * ‖Δ‖ ^ 2 = (1 / 2) * s * (M * s) * ‖Δ‖ ^ 2 := by ring
        _ ≤ (1 / 2) * s * m * ‖Δ‖ ^ 2 := by gcongr
        _ = (1 / 2) * s * (m * ‖Δ‖ ^ 2) := by ring
        _ ≤ (1 / 2) * s * ⟪H x Δ, Δ⟫ :=
          mul_le_mul_of_nonneg_left (hHm x Δ) (mul_nonneg (by norm_num) hs0)
        _ ≤ (1 - α) * s * ⟪H x Δ, Δ⟫ := by
          calc
            (1 / 2) * s * ⟪H x Δ, Δ⟫ = (1 / 2) * (s * ⟪H x Δ, Δ⟫) := by ring
            _ ≤ (1 - α) * (s * ⟪H x Δ, Δ⟫) :=
              mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hs0 hA0)
            _ = (1 - α) * s * ⟪H x Δ, Δ⟫ := by ring
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0, pow_two] at hsmooth
    rw [real_inner_smul_right, hinner] at hsmooth
    rw [hinner]
    ring_nf at hsmooth hquad ⊢
    linarith
  rcases ht with ⟨⟨j, hj⟩, htarmijo, htmax⟩
  have ht0 : 0 ≤ t := by rw [hj]; positivity
  have ht_lower : β * m / M ≤ t := by
    rcases htmax with ht1 | hfail
    · rw [ht1]
      have hmdiv : m / M ≤ 1 := (div_le_one hM).2 hmM
      have hβle : β ≤ 1 := le_of_lt hβ1
      calc
        β * m / M = β * (m / M) := by ring
        _ ≤ 1 * 1 := mul_le_mul hβle hmdiv (div_nonneg (le_of_lt hm) (le_of_lt hM)) (by norm_num)
        _ = 1 := by ring
    · have hprev0 : 0 ≤ t / β := div_nonneg ht0 (le_of_lt hβ0)
      have hprev_gt : m / M < t / β := by
        by_contra hnot
        have hprev_le : t / β ≤ m / M := le_of_not_gt hnot
        exact hfail (harmijo_small (t / β) hprev0 hprev_le)
      have hmul := (lt_div_iff₀ hβ0).mp hprev_gt
      calc
        β * m / M = m / M * β := by ring
        _ ≤ t := le_of_lt hmul
  have hsymm : ∀ u v : EuclideanSpace ℝ (Fin n),
      ⟪H x u, v⟫ = ⟪u, H x v⟫ :=
    fun u v => hessian_symmetric f g hg H hH x u v
  let z : EuclideanSpace ℝ (Fin n) := M • Δ - H x Δ
  have hz0 : 0 ≤ ⟪H x z, z⟫ := by
    exact (mul_nonneg (le_of_lt hm) (sq_nonneg ‖z‖)).trans (hHm x z)
  have hzexpand :
      ⟪H x z, z⟫ = M ^ 2 * ⟪H x Δ, Δ⟫ -
        2 * M * ‖H x Δ‖ ^ 2 + ⟪H x (H x Δ), H x Δ⟫ := by
    dsimp [z]
    simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
    rw [hsymm (H x Δ) Δ]
    rw [real_inner_self_eq_norm_sq]
    ring
  have hC := hHM x (H x Δ)
  have hprod : 0 ≤ M * (M * ⟪H x Δ, Δ⟫ - ‖H x Δ‖ ^ 2) := by
    rw [hzexpand] at hz0
    nlinarith
  have hcoercive : ‖H x Δ‖ ^ 2 ≤ M * ⟪H x Δ, Δ⟫ := by
    have hprod' : 0 ≤ (M * ⟪H x Δ, Δ⟫ - ‖H x Δ‖ ^ 2) * M := by
      simpa [mul_comm] using hprod
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hprod' hM)
  have hdec : ‖g x‖ ^ 2 ≤ M * (-⟪g x, Δ⟫) := by
    calc
      ‖g x‖ ^ 2 = ‖H x Δ‖ ^ 2 := by rw [hΔ]; simp
      _ ≤ M * ⟪H x Δ, Δ⟫ := hcoercive
      _ = M * (-⟪g x, Δ⟫) := by rw [hinner]; ring
  have hη0 : 0 < η := by
    rw [hη]
    have hc : 0 < min 1 (3 * (1 - 2 * α)) := by
      rw [lt_min_iff]
      constructor <;> nlinarith
    positivity
  have hηsq : η ^ 2 ≤ ‖g x‖ ^ 2 := by nlinarith [norm_nonneg (g x)]
  have hdec0 : 0 ≤ -⟪g x, Δ⟫ := by rw [hinner]; linarith
  have hηdec : η ^ 2 / M ≤ -⟪g x, Δ⟫ := by
    apply (div_le_iff₀ hM).2
    simpa [mul_comm] using hηsq.trans hdec
  have hstepdec : α * β * η ^ 2 * m / M ^ 2 ≤ α * t * (-⟪g x, Δ⟫) := by
    calc
      α * β * η ^ 2 * m / M ^ 2 = (α * β * m / M) * (η ^ 2 / M) := by ring
      _ ≤ (α * β * m / M) * (-⟪g x, Δ⟫) := by gcongr
      _ = α * (β * m / M) * (-⟪g x, Δ⟫) := by ring
      _ ≤ α * t * (-⟪g x, Δ⟫) := by gcongr
  ring_nf at htarmijo hstepdec ⊢
  linarith
