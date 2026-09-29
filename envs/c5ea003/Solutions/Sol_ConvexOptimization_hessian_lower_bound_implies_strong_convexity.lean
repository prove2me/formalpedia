-- Prove2me | solution 1 for ConvexOptimization.hessian_lower_bound_implies_strong_convexity
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:20:26.89732+00:00
-- url     : https://prove2.me/submissions/6539bb1a-673b-4cdf-9585-99bd55eee83a

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ} (m : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hH : ∀ x, HasFDerivAt g (H x) x)
    (hm : ∀ x v, m * ‖v‖ ^ 2 ≤ ⟪H x v, v⟫)
    (x y : EuclideanSpace ℝ (Fin n)) :
    f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  set v : EuclideanSpace ℝ (Fin n) := y - x with hv
  set c : ℝ := m * ‖v‖ ^ 2 with hc
  -- The line `ℓ t = x + t • v` and the restriction `φ = f ∘ ℓ` of `f` to it.
  set ℓ : ℝ → EuclideanSpace ℝ (Fin n) := fun t => x + t • v with hℓ
  have hℓd : ∀ t : ℝ, HasDerivAt ℓ v t := fun t => by
    simpa [hℓ] using ((hasDerivAt_id t).smul_const v).const_add x
  set φ : ℝ → ℝ := fun t => f (ℓ t) with hφ
  set dφ : ℝ → ℝ := fun t => ⟪g (ℓ t), v⟫ with hdφ
  have hφd : ∀ t : ℝ, HasDerivAt φ (dφ t) t := fun t =>
    ((hg (ℓ t)).hasFDerivAt).comp_hasDerivAt t (hℓd t)
  have hdφd : ∀ t : ℝ, HasDerivAt dφ (⟪H (ℓ t) v, v⟫) t := fun t =>
    (((innerSL ℝ).flip v).hasFDerivAt).comp_hasDerivAt t
      ((hH (ℓ t)).comp_hasDerivAt t (hℓd t))
  -- The gap `ψ t = φ t − φ 0 − t φ'(0) − (c/2) t²`, whose second derivative is
  -- `⟪H v, v⟫ − m‖v‖² ≥ 0`.
  set dψ : ℝ → ℝ := fun t => dφ t - dφ 0 - c * t with hdψ
  set ψ : ℝ → ℝ := fun t => φ t - φ 0 - t * dφ 0 - c / 2 * (t * t) with hψ
  have hψd : ∀ t : ℝ, HasDerivAt ψ (dψ t) t := by
    intro t
    have h := (((hφd t).sub_const (φ 0)).sub ((hasDerivAt_id t).mul_const (dφ 0))).sub
      (((hasDerivAt_id t).mul (hasDerivAt_id t)).const_mul (c / 2))
    have e : dφ t - 1 * dφ 0 - c / 2 * (1 * t + t * 1) = dψ t := by
      simp only [hdψ]; ring
    rw [← e]
    exact h
  have hdψd : ∀ t : ℝ, HasDerivAt dψ (⟪H (ℓ t) v, v⟫ - c) t := by
    intro t
    have h := ((hdφd t).sub_const (dφ 0)).sub ((hasDerivAt_id t).const_mul c)
    have e : ⟪H (ℓ t) v, v⟫ - c * 1 = ⟪H (ℓ t) v, v⟫ - c := by ring
    rw [← e]
    exact h
  -- `ψ'` is nondecreasing on all of ℝ and vanishes at `0`.
  have hdψmono : Monotone dψ := by
    refine monotone_of_deriv_nonneg (fun t => (hdψd t).differentiableAt) fun t => ?_
    rw [(hdψd t).deriv, hc]
    have := hm (ℓ t) v
    linarith
  have hdψ0 : dψ 0 = 0 := by simp [hdψ]
  -- Hence `ψ` is nondecreasing on `[0, ∞)`, so `ψ 1 ≥ ψ 0 = 0`.
  have hψmono : MonotoneOn ψ (Set.Ici (0 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun t _ => ((hψd t).continuousAt).continuousWithinAt)
      (fun t _ => ((hψd t).differentiableAt).differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici] at ht
    rw [(hψd t).deriv]
    have h := hdψmono (le_of_lt ht)
    rwa [hdψ0] at h
  have hkey : ψ 0 ≤ ψ 1 :=
    hψmono Set.self_mem_Ici (Set.mem_Ici.mpr zero_le_one) zero_le_one
  -- Unfold the endpoints.
  have hφ0 : φ 0 = f x := by simp [hφ, hℓ]
  have hφ1 : φ 1 = f y := by simp [hφ, hℓ, hv]
  have hdφ0 : dφ 0 = ⟪g x, y - x⟫ := by simp [hdφ, hℓ, hv]
  have hψ0 : ψ 0 = 0 := by simp [hψ]
  have hψ1 : ψ 1 = f y - f x - ⟪g x, y - x⟫ - m / 2 * ‖y - x‖ ^ 2 := by
    simp only [hψ, hφ0, hφ1, hdφ0, hc, hv]
    ring
  rw [hψ0, hψ1] at hkey
  linarith
