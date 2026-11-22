-- Prove2me | solution 1 for SimpleGraph.Tree.outwardEdgeCone_nonempty_of_two_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:02.20947+00:00
-- url     : https://prove2.me/submissions/c6e04f49-fd36-4601-9fcc-66f47a6fc610

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_eq_of_target_eq

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
theorem _root_.solution {v : V} (hv : 2 ≤ X.degree v) :
    (X.outwardEdgeCone v₀ v).Nonempty := by
  have : 1 < (X.neighborFinset v).card := by simpa
  rw [Finset.one_lt_card] at this
  obtain ⟨a, ha, b, hb, hne⟩ := this
  rw [mem_neighborFinset] at ha hb
  let ea : X.edgeSet := ⟨s(v, a), ha⟩
  let eb : X.edgeSet := ⟨s(v, b), hb⟩
  have hvea : v ∈ ea.val := by simp [ea]
  have hveb : v ∈ eb.val := by simp [eb]
  rcases eq_source_or_eq_target_of_mem v₀ ea v hvea with h | has
  · use ea
    rw [mem_outwardEdgeCone_iff]
    simpa [h]
  rcases eq_source_or_eq_target_of_mem v₀ eb v hveb with h | hbs
  · use eb
    rw [mem_outwardEdgeCone_iff]
    simpa [h]
  have : ea = eb := by
    apply eq_of_target_eq v₀
    rw [has, hbs]
  absurd hne
  simp only [Subtype.mk.injEq, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk,
    ea, eb] at this
  rcases this with h | h
  · exact h
  · rw [← h.left, h.right]
end SimpleGraph.Tree
