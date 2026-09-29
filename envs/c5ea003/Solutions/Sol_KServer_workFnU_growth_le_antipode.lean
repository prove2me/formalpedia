-- Prove2me | solution 1 for KServer.workFnU_growth_le_antipode
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:40:46.863793+00:00
-- url     : https://prove2.me/submissions/2fb36b0e-76c9-4259-8fe4-b21674e645e4

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz
import Theorems.Thm_KServer_workFnU_duality

open KServer

/-- **The extended cost is absorbed at the antipode of the request.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (N : Type) [MetricSpace N]
    (C₀ : Config k N) (σ : List N) (r rbar : N) (Δ : ℝ)
    (hanti : ∀ y : N, dist y r + dist y rbar = 2 * Δ) (X : Config k N) :
    workFnU C₀ (σ ++ [r]) X - workFnU C₀ σ X
      ≤ workFnU C₀ (σ ++ [r]) (fun _ => rbar) - workFnU C₀ σ (fun _ => rbar) := by
  have hA : ∀ Y : Config k N,
      workFnU C₀ σ (fun _ => rbar) - ∑ i : Fin k, dist r ((fun _ => rbar) i)
        ≤ workFnU C₀ σ Y - ∑ i : Fin k, dist r (Y i) := by
    intro Y
    have hlip := workFnU_lipschitz k hk N C₀ σ (fun _ => rbar) Y
    have hmc : moveCost Y (fun _ => rbar)
        = (k : ℝ) * (2 * Δ) - ∑ i : Fin k, dist r (Y i) := by
      unfold moveCost
      have hterm : ∀ i : Fin k, dist (Y i) rbar = 2 * Δ - dist r (Y i) := by
        intro i
        have h := hanti (Y i)
        rw [dist_comm r (Y i)]
        linarith
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib]
      simp [Finset.card_univ, mul_comm]
    have hconst : (∑ i : Fin k, dist r ((fun _ => rbar) i)) = (k : ℝ) * (2 * Δ) := by
      have h : dist r rbar = 2 * Δ := by
        have := hanti r
        simp only [dist_self] at this
        linarith
      simp [h, Finset.card_univ, mul_comm]
    rw [hconst]
    linarith
  exact (workFnU_duality k hk N C₀ σ r (fun _ => rbar) hA).2 X
