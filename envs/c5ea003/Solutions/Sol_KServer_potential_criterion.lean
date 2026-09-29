-- Prove2me | solution 1 for KServer.potential_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T17:03:06.30382+00:00
-- url     : https://prove2.me/submissions/1ac6706b-fcd2-4aea-8d99-424ac7de1037

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFn_approx_offlineCost

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_self {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFnU C₀ σ X ≤ workFn C₀ σ X := by
  simpa using wfU_le C₀ σ X 1

/-- **The potential-function criterion (Lemma 3).** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ X₀ : Config k M) (hX₀ : Function.Injective X₀) (C : ℝ) (hC : 0 ≤ C)
    (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFnU C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M), Function.Injective X →
      workFnU C₀ (τ ++ [s]) X ≤ workFnU C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A C := by
  have hC1 : (0:ℝ) < C + 1 := by linarith
  have hmain : ∀ σ : List M, ∃ u : ℕ → ℝ,
      (∀ t : ℕ, t < σ.length → ∀ X : Config k M, Function.Injective X →
          workFnU C₀ (σ.take (t + 1)) X ≤ workFnU C₀ (σ.take t) X + u t) ∧
      (∑ t ∈ Finset.range σ.length, u t) ≤ (C + 1) * offlineCost C₀ σ + Φ [] := by
    intro σ
    refine ⟨fun t => Φ (σ.take t) - Φ (σ.take (t + 1)), ?_, ?_⟩
    · intro t ht X hX
      have hsplit : σ.take (t + 1) = σ.take t ++ [σ[t]] := by
        rw [List.take_succ, List.getElem?_eq_getElem ht]
        rfl
      have hu := hUP (σ.take t) σ[t] X hX
      rw [← hsplit] at hu
      simpa using hu
    · have htel : (∑ t ∈ Finset.range σ.length, (Φ (σ.take t) - Φ (σ.take (t + 1))))
          = Φ (σ.take 0) - Φ (σ.take σ.length) :=
        Finset.sum_range_sub' (fun t => Φ (σ.take t)) σ.length
      have key : -Φ σ ≤ (C + 1) * offlineCost C₀ σ := by
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / (C + 1)) (div_pos hε hC1)
        have h1 := hOP σ X
        have h2 : workFnU C₀ σ X ≤ workFn C₀ σ X := wfU_self C₀ σ X
        have h3 : (C + 1) * workFnU C₀ σ X ≤ (C + 1) * (offlineCost C₀ σ + ε / (C + 1)) :=
          mul_le_mul_of_nonneg_left (le_trans h2 hX) (le_of_lt hC1)
        have h4 : (C + 1) * (offlineCost C₀ σ + ε / (C + 1))
            = (C + 1) * offlineCost C₀ σ + ε := by
          field_simp
        linarith
      simp only [htel, List.take_zero, List.take_length]
      linarith
  have h := extended_cost_lemma_injective k hk M C₀ X₀ hX₀ (C + 1) (Φ []) hmain
  simpa using h
