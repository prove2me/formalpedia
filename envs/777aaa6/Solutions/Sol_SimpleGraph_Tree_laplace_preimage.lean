-- Prove2me | solution 1 for SimpleGraph.Tree.laplace_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:04:06.759615+00:00
-- url     : https://prove2.me/submissions/08587fd4-109e-49ff-8892-7fc7b84b4d46

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_P2M_SimpleGraph_Tree_aux_extends__96c9544bd2c3
import Theorems.Thm_SimpleGraph_Tree_aux_spec

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
theorem _root_.solution (hinfinite : ∀ v, (X.outwardEdgeCone v₀ v).Nonempty) :
    X.laplace w (preimage w f v₀) = f := by
  ext v
  simp_rw [laplace, preimage]
  have : ∀ e ∈ incidenceFinset' v, aux w f v₀ (X.dist v₀ (X.target v₀ e)) e =
      aux w f v₀ (X.dist v₀ v + 1) e := by
    intro e he
    rw [mem_incidenceFinset'] at he
    have : X.dist v₀ (X.target v₀ e) ≤ X.dist v₀ v + 1 := by
      rcases eq_source_or_eq_target_of_mem v₀ e v he with h | h
      · subst h
        rw [norm_target_eq_norm_source_add_one]
      · subst h
        simp
    rwa [aux_extends' w f v₀ (X.dist v₀ v + 1)]
  simp_rw [Finset.sum_congr rfl this]
  rw [aux_spec]
  · simp
  · exact hinfinite v
end SimpleGraph.Tree
