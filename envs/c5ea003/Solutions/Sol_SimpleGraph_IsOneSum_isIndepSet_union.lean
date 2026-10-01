-- Prove2me | solution 1 for SimpleGraph.IsOneSum.isIndepSet_union
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:44:57.762614+00:00
-- url     : https://prove2.me/submissions/0b6e580e-0270-4984-b9c3-cff03a0ab486

import Definitions.Def_Novelty_OneSumEqualityAnalysis

set_option autoImplicit false

open SimpleGraph

private lemma soma_unitaria :
    IsOneSum (⊥ : SimpleGraph (ULift.{0} Unit)) ⊥ ⊥ Set.univ Set.univ ⟨()⟩ := by
  constructor
  · simp
  · intro x y adjacencia
    cases adjacencia
  · intro x y adjacencia
    cases adjacencia
  · ext x
    simp
  · simp

theorem solution : ¬ (∀ {W : Type 0} {H H₁ H₂ : SimpleGraph W}
    {C D : Set W} {c : W}, IsOneSum H H₁ H₂ C D c →
    ∀ {V : Type 0} {G G₁ G₂ : SimpleGraph V} {A B : Set V} {v : V}
    [DecidableEq V] {t₁ t₂ : Finset V},
    ↑t₁ ⊆ A → ↑t₂ ⊆ B → G₁.IsIndepSet ↑t₁ → G₂.IsIndepSet ↑t₂ →
    (v ∈ t₁ ↔ v ∈ t₂) → G.IsIndepSet ↑(t₁ ∪ t₂)) := by
  intro alegacao
  have independencia := alegacao soma_unitaria
    (V := ULift.{0} (Fin 2)) (G := ⊤) (G₁ := ⊥) (G₂ := ⊥)
    (A := Set.univ) (B := Set.univ) (v := ⟨0⟩)
    (t₁ := Finset.univ) (t₂ := Finset.univ)
    (by simp) (by simp) (by intro a ha b hb hab adj; cases adj)
    (by intro a ha b hb hab adj; cases adj) Iff.rfl
  have nao_adjacentes := independencia
    (x := (⟨0⟩ : ULift.{0} (Fin 2))) (by simp)
    (y := (⟨1⟩ : ULift.{0} (Fin 2))) (by simp) (by decide)
  exact nao_adjacentes (by decide)
