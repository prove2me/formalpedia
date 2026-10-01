-- Prove2me | solution 1 for SimpleGraph.IsOneSum.indepRatio_ge_of_sides
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:45:00.983978+00:00
-- url     : https://prove2.me/submissions/268086b7-1d09-4509-9f2b-150e5a4b8532

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
    [DecidableEq V] [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)]
    {s₁ s₂ : Finset V}, ↑s₁ ⊆ A → ↑s₂ ⊆ B →
    G₁.IsIndepSet ↑s₁ → G₂.IsIndepSet ↑s₂ → ∀ {r : ℚ},
    r * ((Finset.univ.filter (· ∈ A)).card : ℚ) ≤ (s₁.card : ℚ) →
    r * ((Finset.univ.filter (· ∈ B)).card : ℚ) ≤ (s₂.card : ℚ) →
    0 < Fintype.card V →
    r - (1 - r) / (Fintype.card V : ℚ) ≤ G.indepRatio) := by
  intro alegacao
  have limite := alegacao soma_unitaria
    (V := ULift.{0} (Fin 2)) (G := ⊤) (G₁ := ⊥) (G₂ := ⊥)
    (A := Set.univ) (B := Set.univ) (s₁ := Finset.univ) (s₂ := Finset.univ)
    (by simp) (by simp)
    (by intro a ha b hb hab adj; cases adj)
    (by intro a ha b hb hab adj; cases adj)
    (r := 1) (by simp) (by simp) (by simp)
  have superior : ((⊤ : SimpleGraph (ULift.{0} (Fin 2))).indepNum : ℚ) ≤ 1 := by
    exact_mod_cast independencia_completo_le_um (ULift.{0} (Fin 2))
  norm_num [SimpleGraph.indepRatio] at limite
  linarith
