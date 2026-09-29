-- Prove2me | solution 1 for KServer.workFn_workFnU_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T21:42:13.879549+00:00
-- url     : https://prove2.me/submissions/4e47d31d-06a6-44d8-a4ab-4a32a7624bb0

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_lipschitz

open KServer

/-- **The labelled and unlabelled work functions are within `k·Δ` of one another.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) (Δ : ℝ)
    (hΔ : ∀ u v : M, dist u v ≤ Δ) :
    workFnU C₀ σ X ≤ workFn C₀ σ X ∧ workFn C₀ σ X ≤ workFnU C₀ σ X + k * Δ := by
  have hmc : ∀ π : Equiv.Perm (Fin k), moveCost (X ∘ π) X ≤ k * Δ := by
    intro π
    unfold moveCost
    calc ∑ i, dist ((X ∘ π) i) (X i)
        ≤ ∑ _i : Fin k, Δ := Finset.sum_le_sum fun i _ => hΔ _ _
      _ = k * Δ := by simp [mul_comm]
  refine ⟨?_, ?_⟩
  · have := ciInf_le (f := fun π : Equiv.Perm (Fin k) => workFn C₀ σ (X ∘ π))
      (Finite.bddBelow_range _) (1 : Equiv.Perm (Fin k))
    simpa [workFnU] using this
  · have hb : ∀ π : Equiv.Perm (Fin k), workFn C₀ σ X - k * Δ ≤ workFn C₀ σ (X ∘ π) := by
      intro π
      have h := workFn_lipschitz k hk M C₀ σ X (X ∘ π)
      linarith [hmc π]
    have : workFn C₀ σ X - k * Δ ≤ workFnU C₀ σ X := le_ciInf hb
    linarith
