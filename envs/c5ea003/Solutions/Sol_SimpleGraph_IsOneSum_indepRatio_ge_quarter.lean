-- Prove2me | solution 1 for SimpleGraph.IsOneSum.indepRatio_ge_quarter
-- status  : ACCEPTED   (disprove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:45:03.200024+00:00
-- url     : https://prove2.me/submissions/1ab82459-3047-4375-83be-ae9bf06b5533

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
    ∀ {V : Type 0} [Fintype V] {G G₁ G₂ : SimpleGraph V},
    0 < Fintype.card V → G₁.Colorable 4 → G₂.Colorable 4 →
    (1 : ℚ) / 4 ≤ G.indepRatio) := by
  intro alegacao
  have coloracao : (⊥ : SimpleGraph (ULift.{0} (Fin 5))).Colorable 4 := by
    refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 4)) ?_⟩
    intro x y adjacencia
    cases adjacencia
  have limite := alegacao soma_unitaria
    (V := ULift.{0} (Fin 5)) (G := ⊤) (G₁ := ⊥) (G₂ := ⊥)
    (by simp) coloracao coloracao
  have superior : ((⊤ : SimpleGraph (ULift.{0} (Fin 5))).indepNum : ℚ) ≤ 1 := by
    exact_mod_cast independencia_completo_le_um (ULift.{0} (Fin 5))
  norm_num [SimpleGraph.indepRatio] at limite
  linarith
