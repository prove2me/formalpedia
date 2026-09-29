-- Prove2me | solution 1 for PhantomTopology.sierp_sup_eq_indiscrete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:50:33.064496+00:00
-- url     : https://prove2.me/submissions/8c18ab6b-59ea-433e-905f-b880e19afbcb

-- Sol generated from Logic/PosetTheory/PhantomTopologies.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_PhantomTopologies
/-
# Phantom Topologies

A phantom topology is an observer-indexed family of topologies.  This file makes
"agreement" precise as the supremum in Mathlib's (reverse-inclusion) lattice of
topologies and develops a chain of results from the general definition to two
substantive examples.

The literal proposed phantom number is degenerate: every topology has a
one-observer representation, obtained by letting that observer see the real
topology itself.  A nontrivial variant requires every observer to be strictly
finer than consensus.  For that variant, the standard topology on `ℝ` has a
genuine two-observer representation by the lower- and upper-limit topologies.
The proposed lower bound for nonmetrizable spaces is false: the indiscrete
space on `Bool` is nonmetrizable yet is the consensus of two strictly finer
Sierpiński topologies.
-/

open Set TopologicalSpace

open PhantomTopology

variable {X ι : Type*}










/-! ## The real line: two half-open observers -/















/-! ## A nonmetrizable two-observer counterexample -/










open PhantomTopology in
theorem solution:
    sierpTrue ⊔ sierpFalse = (⊤ : TopologicalSpace Bool) := by
  apply TopologicalSpace.ext
  ext U
  rw [isOpen_top_iff]
  constructor
  · rintro ⟨hT, hF⟩
    by_cases hne : U = ∅
    · exact Or.inl hne
    · refine Or.inr ?_
      obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.2 hne
      have ht : true ∈ U := by
        cases x with
        | false => exact hT hx
        | true => exact hx
      have hf : false ∈ U := hF ht
      ext y
      cases y <;> simp_all
  · rintro (rfl | rfl)
    · exact @isOpen_empty Bool (sierpTrue ⊔ sierpFalse)
    · exact @isOpen_univ Bool (sierpTrue ⊔ sierpFalse)
