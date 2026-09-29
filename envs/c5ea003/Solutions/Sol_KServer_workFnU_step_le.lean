-- Prove2me | solution 1 for KServer.workFnU_step_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:00:15.318289+00:00
-- url     : https://prove2.me/submissions/f3394d04-c780-46b3-b294-d341a739dfaa

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_step_le
import Theorems.Thm_KServer_workFnU_perm

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

/-- **One step of the unordered work-function recurrence, upper half.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z Y : Config k M) (hY : ∃ i, Y i = r) :
    workFnU C₀ (σ ++ [r]) Z ≤ workFnU C₀ σ Y + moveCost Y Z := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ σ Y
  have hcov : ∃ i, (Y ∘ (π : Equiv.Perm (Fin k))) i = r := by
    obtain ⟨i, hi⟩ := hY
    exact ⟨π.symm i, by simpa using hi⟩
  have h1 := wfU_self C₀ (σ ++ [r]) (Z ∘ (π : Equiv.Perm (Fin k)))
  have h2 := workFn_step_le k hk M C₀ σ r (Z ∘ (π : Equiv.Perm (Fin k)))
    (Y ∘ (π : Equiv.Perm (Fin k))) hcov
  have h3 := mc_perm Y Z π
  have h4 := workFnU_perm k M C₀ (σ ++ [r]) Z π
  linarith
