-- Prove2me | solution 1 for SimpleGraph.Tree.source_eq_of_target_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:39.843273+00:00
-- url     : https://prove2.me/submissions/21b69039-b3b7-4fee-a580-dab74b36ffa5

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_dist_eq_of_isPath

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
omit [DecidableEq V] [(v : V) → Fintype ↑(X.neighborSet v)]
namespace SimpleGraph.Tree
theorem _root_.solution (e f : X.edgeSet) (h : X.target v₀ e = X.target v₀ f) :
    X.source v₀ e = X.source v₀ f := by
  obtain ⟨p, hp, hplen⟩ := X.isTree.isConnected.exists_path_of_dist (X.source v₀ e) v₀
  let headj : X.Adj (source v₀ e) (target v₀ e) := source_adj_target v₀ e
  obtain ⟨q, hq, hqlen⟩ := X.isTree.isConnected.exists_path_of_dist (X.source v₀ f) v₀
  let hfadj : X.Adj (source v₀ f) (target v₀ e) := by
    rw [h]
    exact source_adj_target v₀ f
  let p' : X.Walk (target v₀ e) v₀ := p.cons headj.symm
  have hp' : p'.IsPath := by
    simp only [Walk.cons_isPath_iff, hp, true_and, p']
    intro hc
    obtain ⟨r, hr, hpr⟩ := exists_path_eq_cons_of_isPath_of_mem_support v₀ headj p hc hp
    have : X.dist v₀ (source v₀ e) = X.dist v₀ (target v₀ e) + 1 := by
      rw [dist_comm, ← hplen, hpr, dist_comm, dist_eq_of_isPath r hr]
      simp
    rw [norm_target_eq_norm_source_add_one] at this
    omega
  let q' : X.Walk (target v₀ e) v₀ := q.cons hfadj.symm
  have hq' : q'.IsPath := by
    simp only [Walk.cons_isPath_iff, hq, true_and, q']
    intro hc
    obtain ⟨r, hr, hpr⟩ := exists_path_eq_cons_of_isPath_of_mem_support v₀ hfadj q hc hq
    have : X.dist v₀ (source v₀ f) = X.dist v₀ (target v₀ f) + 1 := by
      rw [← h]
      rw [dist_comm, ← hqlen, hpr, dist_comm, dist_eq_of_isPath r hr]
      simp
    rw [norm_target_eq_norm_source_add_one] at this
    omega
  let p'' : X.Path (target v₀ e) v₀ := ⟨p', hp'⟩
  let q'' : X.Path (target v₀ e) v₀ := ⟨q', hq'⟩
  have : p'' = q'' := X.isTree.IsAcyclic.path_unique _ _
  simp only [Subtype.mk.injEq, Walk.cons.injEq, p'', p', q'', q'] at this
  exact this.left
end SimpleGraph.Tree
