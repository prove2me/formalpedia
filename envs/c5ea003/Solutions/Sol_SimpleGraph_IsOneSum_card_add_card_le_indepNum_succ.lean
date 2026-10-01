-- Prove2me | solution 1 for SimpleGraph.IsOneSum.card_add_card_le_indepNum_succ
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:44:59.110659+00:00
-- url     : https://prove2.me/submissions/f2f8b4b1-e795-4433-a44c-7b7f75a3d88c

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

private lemma independencia_completo_le_um (V : Type 0) :
    (⊤ : SimpleGraph V).indepNum ≤ 1 := by
  classical
  obtain ⟨s, independencia, cardinalidade⟩ :=
    (⊤ : SimpleGraph V).exists_isNIndepSet_indepNum
  rw [← cardinalidade]
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra distintos
  exact independencia hx hy distintos distintos

theorem solution : ¬ (∀ {W : Type 0} {H H₁ H₂ : SimpleGraph W}
    {C D : Set W} {c : W}, IsOneSum H H₁ H₂ C D c →
    ∀ {V : Type 0} [Fintype V] {G G₁ G₂ : SimpleGraph V} {A B : Set V}
    [DecidableEq V] {s₁ s₂ : Finset V},
    ↑s₁ ⊆ A → ↑s₂ ⊆ B → G₁.IsIndepSet ↑s₁ → G₂.IsIndepSet ↑s₂ →
    s₁.card + s₂.card ≤ G.indepNum + 1) := by
  intro alegacao
  have limite := alegacao soma_unitaria
    (V := ULift.{0} (Fin 2)) (G := ⊤) (G₁ := ⊥) (G₂ := ⊥)
    (A := Set.univ) (B := Set.univ) (s₁ := Finset.univ) (s₂ := Finset.univ)
    (by simp) (by simp)
    (by intro a ha b hb hab adj; cases adj)
    (by intro a ha b hb hab adj; cases adj)
  have superior := independencia_completo_le_um (ULift.{0} (Fin 2))
  simp only [Finset.card_univ, Fintype.card_ulift, Fintype.card_fin] at limite
  omega
