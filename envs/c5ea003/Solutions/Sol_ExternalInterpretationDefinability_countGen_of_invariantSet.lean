-- Prove2me | solution 1 for ExternalInterpretationDefinability.countGen_of_invariantSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:27:30.376887+00:00
-- url     : https://prove2.me/submissions/4d98a077-f7a0-4af7-b81a-69340dcaf5e5

import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
open ExternalInterpretationDefinability in
theorem solution {G : Type*} {M : Type*} [Group G] [MulAction G M] [Finite M] {s : Set M}
    (hs : InvariantSet G s) : CountGen G M s := by
  classical
  -- finite unions of orbits are countably generated
  have hFin : ∀ F : Finset M, CountGen G M (⋃ x ∈ F, MulAction.orbit G x) := by
    intro F
    refine Finset.induction_on F ?_ ?_
    · simpa using CountGen.empty
    · intro x F _ ih
      rw [Finset.set_biUnion_insert]
      exact CountGen.union (CountGen.orbit x) ih
  -- an invariant set is the union of the orbits of its points
  have hs_fin : s.Finite := Set.toFinite s
  have heq : s = ⋃ x ∈ hs_fin.toFinset, MulAction.orbit G x := by
    ext y
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · intro hy
      exact ⟨y, hy, MulAction.mem_orbit_self y⟩
    · rintro ⟨x, hx, ⟨g, rfl⟩⟩
      exact hs g hx
  rw [heq]
  exact hFin _
