-- Prove2me | solution 1 for PosetFlow.chainFinsets_self
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T03:37:31.516968+00:00
-- url     : https://prove2.me/submissions/a33b381f-e9e3-4fde-8423-311af03346f0

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    (x : P) : chainFinsets x x = {{x}} := by
  ext C
  simp only [chainFinsets, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, -, hb, -⟩
    -- antisymmetry collapses every element of the chain to `x`
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hx, ?_⟩
    intro a ha
    exact le_antisymm (hb a ha).2 (hb a ha).1
  · rintro rfl
    refine ⟨Finset.mem_singleton_self x, Finset.mem_singleton_self x, ?_, ?_⟩
    · intro a ha
      rw [Finset.mem_singleton] at ha
      subst ha
      exact ⟨le_refl _, le_refl _⟩
    · intro a ha b hb
      rw [Finset.mem_singleton] at ha hb
      subst ha
      subst hb
      exact Or.inl (le_refl _)
