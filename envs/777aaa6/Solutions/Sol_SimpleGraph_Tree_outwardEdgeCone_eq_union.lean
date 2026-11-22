-- Prove2me | solution 1 for SimpleGraph.Tree.outwardEdgeCone_eq_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:45.46135+00:00
-- url     : https://prove2.me/submissions/a85256c0-a062-46f6-8ed2-d2c2cc1fa7cc

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
namespace SimpleGraph.Tree
theorem _root_.solution (w : V) (hw : (X.outwardEdgeCone v₀ w).Nonempty) :
    X.outwardEdgeCone v₀ w = { X.distinguishedEdge v₀ w hw } ∪
        { e | e ∈ X.outwardEdgeCone v₀ w ∧ X.distinguishedEdge v₀ w hw ≠ e } := by
  ext e
  simp_rw [Finset.mem_coe, ne_eq, Set.singleton_union, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    by_cases hde : e = distinguishedEdge v₀ w hw
    · exact Or.inl hde
    · exact Or.inr ⟨h, fun a ↦ hde a.symm⟩
  · rintro ⟨_, _⟩
    · exact distinguishedEdge_mem v₀ w hw
    · next h => exact h.left
end SimpleGraph.Tree
