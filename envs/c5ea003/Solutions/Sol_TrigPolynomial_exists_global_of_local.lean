-- Prove2me | solution 1 for TrigPolynomial.exists_global_of_local
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-28T00:01:06.024597+00:00
-- url     : https://prove2.me/submissions/1d389e98-a055-4cfc-99bf-62dbdd28d897

import Mathlib
import Theorems.Thm_TrigPolynomial_coeffs_eq_zero_of_eventually_eq_zero

open Filter Topology

theorem solution (k : ℝ) (hk : k ≠ 0) (q : ℝ → ℝ) (delta : ℝ) (hd : 0 < delta)
    (Dc Ac Bc : ℝ → ℝ)
    (hrep : ∀ t0 t : ℝ, |t - t0| < delta →
      q t = Dc t0 + Ac t0 * Real.cos (k * t) + Bc t0 * Real.sin (k * t)) :
    ∃ D A B : ℝ, ∀ t : ℝ, q t = D + A * Real.cos (k * t) + B * Real.sin (k * t) := by
  classical
  set F : ℝ → ℝ × ℝ × ℝ := fun t => (Dc t, Ac t, Bc t) with hF
  have key : ∀ t0 t1 : ℝ, |t1 - t0| < delta / 2 → F t1 = F t0 := by
    intro t0 t1 hlt
    have hnear : ∀ᶠ x in 𝓝 t1,
        (Dc t0 - Dc t1) + (Ac t0 - Ac t1) * Real.cos (k * x)
          + (Bc t0 - Bc t1) * Real.sin (k * x) = 0 := by
      have hball : Metric.ball t1 (delta / 2) ∈ 𝓝 t1 :=
        Metric.ball_mem_nhds t1 (by linarith)
      filter_upwards [hball] with x hx
      have hx1 : |x - t1| < delta / 2 := by
        have := Metric.mem_ball.mp hx
        rwa [Real.dist_eq] at this
      have hx0 : |x - t0| < delta := by
        have habs : |x - t0| ≤ |x - t1| + |t1 - t0| := by
          have : x - t0 = (x - t1) + (t1 - t0) := by ring
          rw [this]; exact abs_add_le _ _
        have h2 : |t1 - t0| < delta / 2 := hlt
        linarith
      have e0 := hrep t0 x hx0
      have e1 := hrep t1 x (by linarith [hx1] : |x - t1| < delta)
      linarith [e0, e1]
    obtain ⟨hD, hA, hB⟩ := TrigPolynomial.coeffs_eq_zero_of_eventually_eq_zero k hk _ _ _ t1 hnear
    simp only [hF, Prod.mk.injEq]
    refine ⟨by linarith, by linarith, by linarith⟩
  set S : Set ℝ := {t | F t = F 0} with hS
  have hopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro t0 ht0
    refine ⟨delta / 2, by linarith, fun t ht => ?_⟩
    have ht' : |t - t0| < delta / 2 := by
      have := Metric.mem_ball.mp ht; rwa [Real.dist_eq] at this
    have hkey := key t0 t ht'
    simp only [hS, Set.mem_setOf_eq] at ht0 ⊢
    rw [hkey]; exact ht0
  have hclosed : IsOpen Sᶜ := by
    rw [Metric.isOpen_iff]
    intro t0 ht0
    refine ⟨delta / 2, by linarith, fun t ht => ?_⟩
    have ht' : |t - t0| < delta / 2 := by
      have := Metric.mem_ball.mp ht; rwa [Real.dist_eq] at this
    have hkey := key t0 t ht'
    simp only [hS, Set.mem_compl_iff, Set.mem_setOf_eq] at ht0 ⊢
    rw [hkey]; exact ht0
  have hall : S = Set.univ := by
    refine IsClopen.eq_univ ⟨isOpen_compl_iff.mp hclosed, hopen⟩ ⟨0, by simp [hS]⟩
  refine ⟨Dc 0, Ac 0, Bc 0, fun t => ?_⟩
  have ht : F t = F 0 := by
    have : t ∈ S := by rw [hall]; trivial
    simpa [hS] using this
  have hq := hrep t t (by simpa using hd)
  simp only [hF, Prod.mk.injEq] at ht
  rw [hq, ht.1, ht.2.1, ht.2.2]
