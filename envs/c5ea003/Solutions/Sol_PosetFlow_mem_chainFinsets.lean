-- Prove2me | solution 1 for PosetFlow.mem_chainFinsets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:10:33.39691+00:00
-- url     : https://prove2.me/submissions/d8b7d79d-5379-4ee4-8494-3fb9b8165b4b

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [Fintype P] [DecidableEq P] [DecidableLE P]
    {x y : P} {C : Finset P} :
    C ∈ chainFinsets x y ↔
      x ∈ C ∧ y ∈ C ∧ (∀ a ∈ C, x ≤ a ∧ a ≤ y) ∧ (∀ a ∈ C, ∀ b ∈ C, a ≤ b ∨ b ≤ a) := by
  simp only [chainFinsets, Finset.mem_filter, Finset.mem_univ, true_and]
