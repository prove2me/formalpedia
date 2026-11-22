-- Prove2me | solution 1 for SimpleGraph.Tree.incidenceFinset_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:36.987813+00:00
-- url     : https://prove2.me/submissions/fb47f6b2-0841-4279-a8c3-a4fcf625c0a7

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_eq_edgeTowardsOrigin_iff_of_mem
import Theorems.Thm_SimpleGraph_Tree_vertex_mem_edgeTowardsOrigin

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
variable (n : ℕ) (g : X.edgeSet → M)
namespace SimpleGraph.Tree
theorem _root_.solution (v : V) (hv : 0 < X.dist v₀ v) :
    X.incidenceFinset' v = { edgeTowardsOrigin v₀ v hv } ∪ X.outwardEdgeCone v₀ v := by
  ext e
  constructor
  · intro h
    simp only [Finset.mem_union, Finset.mem_singleton]
    by_cases heq : edgeTowardsOrigin v₀ v hv = e
    · exact Or.inl heq.symm
    · apply Or.inr
      rw [mem_incidenceFinset'] at h
      rw [mem_outwardEdgeCone_iff]
      constructor
      · exact h
      · /- conclude using that `e` is not the edge towards the origin. -/
        rcases eq_source_or_eq_target_of_mem v₀ e v h with h₂ | h₂
        · exact h₂
        · rw [← eq_edgeTowardsOrigin_iff_of_mem v₀ v hv e h] at h₂
          absurd h₂
          exact fun hc ↦ heq hc.symm
  · intro h
    simp only [Finset.mem_union, Finset.mem_singleton] at h
    cases h
    · next h =>
      subst h
      rw [mem_incidenceFinset']
      apply vertex_mem_edgeTowardsOrigin
    · next h =>
      rw [mem_incidenceFinset']
      rw [mem_outwardEdgeCone_iff] at h
      exact h.left
end SimpleGraph.Tree
