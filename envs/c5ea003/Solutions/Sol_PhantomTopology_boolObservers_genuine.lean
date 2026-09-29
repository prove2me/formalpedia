-- Prove2me | solution 1 for PhantomTopology.boolObservers_genuine
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:52:12.062187+00:00
-- url     : https://prove2.me/submissions/a81530ba-a866-4351-878d-98605155a902

-- Sol generated from Logic/PosetTheory/PhantomTopologies.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_PhantomTopologies
import Theorems.Thm_PhantomTopology_sierp_sup_eq_indiscrete
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






/-- Their consensus is indiscrete. -/
theorem bool_consensus_eq_indiscrete :
    consensus boolObservers = (⊤ : TopologicalSpace Bool) := by
  rw [consensus, iSup_bool_eq]
  exact sierp_sup_eq_indiscrete




open PhantomTopology in
theorem solution: Genuine boolObservers := by
  intro b
  rw [bool_consensus_eq_indiscrete]
  cases b
  · simp only [boolObservers, Bool.false_eq]
    refine lt_of_le_of_ne le_top ?_
    intro h
    have ho : @IsOpen Bool sierpFalse {false} := by intro ht; simp at ht
    have : @IsOpen Bool (⊤ : TopologicalSpace Bool) {false} := h ▸ ho
    rw [isOpen_top_iff] at this
    rcases this with h0 | h1
    · exact Set.singleton_ne_empty false h0
    · have : true ∈ ({false} : Set Bool) := by rw [h1]; trivial
      simp at this
  · simp only [boolObservers, ↓reduceIte]
    refine lt_of_le_of_ne le_top ?_
    intro h
    have ho : @IsOpen Bool sierpTrue {true} := by intro hf; simp at hf
    have : @IsOpen Bool (⊤ : TopologicalSpace Bool) {true} := h ▸ ho
    rw [isOpen_top_iff] at this
    rcases this with h0 | h1
    · exact Set.singleton_ne_empty true h0
    · have : false ∈ ({true} : Set Bool) := by rw [h1]; trivial
      simp at this
