-- Prove2me | solution 1 for SimpleGraph.Tree.aux_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:03:32.325058+00:00
-- url     : https://prove2.me/submissions/0444de4d-e3fc-4071-93d8-aeceb6464b82

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_outwardEdgeCone_origin_eq
import Theorems.Thm_SimpleGraph_Tree_edgeTowardsOrigin_not_mem_outwardEdgeCone
import Theorems.Thm_SimpleGraph_Tree_incidenceFinset_eq_union
import Theorems.Thm_SimpleGraph_Tree_aux_spec_origin_distinguishedEdge
import Theorems.Thm_SimpleGraph_Tree_aux_spec_outwardEdgeCone_erase
import Theorems.Thm_SimpleGraph_Tree_aux_spec_distinguishedEdge

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
theorem _root_.solution (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    w v • ∑ e ∈ X.incidenceFinset' v, aux w f v₀ n e = f v := by
  match n with
  | 0 =>
    /- the impossible case -/
    simp at hv
  | 1 =>
    /- the case `v = v₀` -/
    simp_rw [add_eq_right, dist_eq_zero_iff_eq_or_not_reachable] at hv
    have : X.Reachable v₀ v := X.isTree.isConnected.preconnected v₀ v
    have : v₀ = v := by tauto
    subst this
    simp_rw [← outwardEdgeCone_origin_eq]
    let ed : X.edgeSet := X.distinguishedEdge v₀ v₀ hnonempty
    have hed : ed ∈ X.outwardEdgeCone v₀ v₀ := distinguishedEdge_mem v₀ v₀ hnonempty
    rw [← Finset.insert_erase hed]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
      Finset.sum_insert]
    rw [aux_spec_outwardEdgeCone_erase]
    · simp_rw [add_zero, ed]
      rw [aux_spec_origin_distinguishedEdge]
      simp
    · simp
  | n + 2 =>
    /- the case `v ≠ v₀` -/
    have hdist : 0 < X.dist v₀ v := by
      rw [add_left_inj] at hv
      omega
    simp_rw [incidenceFinset_eq_union v₀ v hdist]
    rw [Finset.sum_union]
    simp only [Finset.sum_singleton]
    let ed : X.edgeSet := X.distinguishedEdge v₀ v hnonempty
    have hed : ed ∈ X.outwardEdgeCone v₀ v := distinguishedEdge_mem v₀ v hnonempty
    rw [← Finset.insert_erase hed]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, Finset.sum_insert]
    rw [aux_spec_outwardEdgeCone_erase]
    · simp only [add_zero, smul_add, ed]
      rw [aux_spec_distinguishedEdge _ _ _ _ _ hv hdist, smul_sub]
      simp
    · simpa using hv
    simp only [Finset.disjoint_singleton_left]
    apply edgeTowardsOrigin_not_mem_outwardEdgeCone
end SimpleGraph.Tree
