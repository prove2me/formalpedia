-- Prove2me | solution 1 for KServer.wfaU_potential_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:15:50.578371+00:00
-- url     : https://prove2.me/submissions/ebfd1d9a-2295-435e-9566-11a6a6c14f44

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_wfaU
import Theorems.Thm_KServer_wfaU_cost_le_growth
import Theorems.Thm_KServer_workFn_approx_offlineCost

open KServer

private theorem wfU_le_wf {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  have h := ciInf_le (f := fun π : Equiv.Perm (Fin k) => workFn C₀ σ (X ∘ π))
    (Finite.bddBelow_range _) (1 : Equiv.Perm (Fin k))
  simpa [workFnU] using h

/-- **The potential-function criterion for the classical Work Function Algorithm.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFAU hk C₀) C := by
  have hC1 : (0:ℝ) < C + 1 := by linarith
  refine ⟨Φ [], fun σ => ?_⟩
  have hgrowth : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFnU C₀ (σ.take (t + 1)) X
        ≤ workFnU C₀ (σ.take t) X + (Φ (σ.take t) - Φ (σ.take (t + 1))) := by
    intro t ht X
    have hsplit : σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
      rw [List.take_succ, List.getElem?_eq_getElem ht]
      rfl
    rw [hsplit]
    exact hUP (σ.take t) (σ[t]'ht) X
  have hmain := wfaU_cost_le_growth k hk M C₀ σ
    (fun t => Φ (σ.take t) - Φ (σ.take (t + 1))) hgrowth
  have htel : (∑ t ∈ Finset.range σ.length, (Φ (σ.take t) - Φ (σ.take (t + 1))))
      = Φ (σ.take 0) - Φ (σ.take σ.length) :=
    Finset.sum_range_sub' (fun t => Φ (σ.take t)) σ.length
  have key : -Φ σ ≤ (C + 1) * offlineCost C₀ σ := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / (C + 1)) (div_pos hε hC1)
    have h1 := hOP σ X
    have h2 : workFnU C₀ σ X ≤ workFn C₀ σ X := wfU_le_wf C₀ σ X
    have h3 : (C + 1) * workFnU C₀ σ X ≤ (C + 1) * (offlineCost C₀ σ + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left (le_trans h2 hX) (le_of_lt hC1)
    have h4 : (C + 1) * (offlineCost C₀ σ + ε / (C + 1))
        = (C + 1) * offlineCost C₀ σ + ε := by field_simp
    linarith
  have hconf : (WFAU hk C₀).conf [] = C₀ := WFAU_conf_nil hk C₀
  rw [hconf]
  simp only [htel, List.take_zero, List.take_length] at hmain
  linarith
