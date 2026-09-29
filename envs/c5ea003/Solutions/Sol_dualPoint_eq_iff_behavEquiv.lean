-- Prove2me | solution 1 for dualPoint_eq_iff_behavEquiv
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T07:00:18.280985+00:00
-- url     : https://prove2.me/submissions/177e78f7-d1b3-45e8-826c-6caef6b233cc

import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalStoneSemiringBridge

open Set

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem solution (T : FTS σ) (V : ℕ → Set σ) (s t : σ) :
    DualPoint T V s = DualPoint T V t ↔ BehavioralEquiv T V s t := by
  constructor
  · intro h φ
    have key (u : σ) :
        u ∈ TFormula.eval T V φ ↔ TFormula.eval T V φ ∈ DualPoint T V u := by
      simp [DualPoint, DefinablePreds]
    rw [key s, h, ← key t]
  · intro h
    ext X
    simp only [DualPoint, mem_setOf_eq]
    constructor
    · rintro ⟨⟨φ, rfl⟩, hs⟩
      exact ⟨⟨φ, rfl⟩, (h φ).mp hs⟩
    · rintro ⟨⟨φ, rfl⟩, ht⟩
      exact ⟨⟨φ, rfl⟩, (h φ).mpr ht⟩
