-- Prove2me | solution 1 for KServer.workFnU_dual_pair_exchange
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:55:15.529471+00:00
-- url     : https://prove2.me/submissions/6c10deed-659e-497c-a63c-da0bc1f31261

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_perm
import Theorems.Thm_KServer_workFnU_quasiconvex_three

open KServer

private theorem swap12M {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (p q c : M) : workFnU C₀ σ ![p, q, c] = workFnU C₀ σ ![p, c, q] := by
  have h : (![p, q, c] : Config 3 M) = ![p, c, q] ∘ (Equiv.swap (1 : Fin 3) 2) := by
    funext i
    match i with
    | 0 => show p = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 0)
           rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]; rfl
    | 1 => show q = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 1); rw [Equiv.swap_apply_left]; rfl
    | 2 => show c = ![p, c, q] ((Equiv.swap (1 : Fin 3) 2) 2); rw [Equiv.swap_apply_right]; rfl
  rw [h]
  exact workFnU_perm 3 M C₀ σ ![p, c, q] (Equiv.swap 1 2)

/-- **The greedy exchange for the dual pair functional.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (x₂ x₃ x₁ p q : M)
    (hx₁ : ∀ u : M, workFnU C₀ σ ![x₃, x₁, x₂] - dist x₁ x₂
        ≤ workFnU C₀ σ ![x₃, u, x₂] - dist u x₂)
    (hpq : ∀ u v : M, workFnU C₀ σ ![x₃, p, q] - dist p x₂ - dist q x₂
        ≤ workFnU C₀ σ ![x₃, u, v] - dist u x₂ - dist v x₂) :
    ∃ w : M, ∀ u v : M,
      workFnU C₀ σ ![x₃, x₁, w] - dist x₁ x₂ - dist w x₂
        ≤ workFnU C₀ σ ![x₃, u, v] - dist u x₂ - dist v x₂ := by
  have qc := workFnU_quasiconvex_three M C₀ σ x₃ x₁ x₂ p q
  rcases min_cases (workFnU C₀ σ ![x₃, x₁, p] + workFnU C₀ σ ![x₃, x₂, q])
      (workFnU C₀ σ ![x₃, x₁, q] + workFnU C₀ σ ![x₃, x₂, p]) with ⟨he, -⟩ | ⟨he, -⟩ <;>
    rw [he] at qc
  · -- pairing (x₁,p) + (x₂,q): the witness is p
    refine ⟨p, fun u v => ?_⟩
    have h1 := hx₁ q
    rw [swap12M C₀ σ x₃ q x₂] at h1
    have h2 := hpq u v
    linarith
  · -- pairing (x₁,q) + (x₂,p): the witness is q
    refine ⟨q, fun u v => ?_⟩
    have h1 := hx₁ p
    rw [swap12M C₀ σ x₃ p x₂] at h1
    have h2 := hpq u v
    linarith
