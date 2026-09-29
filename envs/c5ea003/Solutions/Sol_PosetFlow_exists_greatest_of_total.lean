-- Prove2me | solution 1 for PosetFlow.exists_greatest_of_total
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T13:44:33.297132+00:00
-- url     : https://prove2.me/submissions/99c24aa0-30dd-4069-b8e9-6f5afc3c0a3b

import Mathlib
import Definitions.Def_Algebra_PosetFlow_ChainPoset
import Definitions.Def_Algebra_PosetFlow_HallMobius
open PosetFlow Finset IncidenceAlgebra in
theorem solution {P : Type*} [PartialOrder P] [DecidableEq P]
    (S : Finset P) (hne : S.Nonempty)
    (htot : ∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) : ∃ z ∈ S, ∀ a ∈ S, a ≤ z := by
  -- a maximal element of a totally ordered finite set is its greatest element
  obtain ⟨z, hz⟩ := Finset.exists_maximal hne
  refine ⟨z, hz.1, fun a ha => ?_⟩
  rcases htot a ha z hz.1 with h | h
  · exact h
  · exact hz.2 ha h
