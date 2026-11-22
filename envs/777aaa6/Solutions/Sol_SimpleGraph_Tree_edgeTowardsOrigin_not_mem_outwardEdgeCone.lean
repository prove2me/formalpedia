-- Prove2me | solution 1 for SimpleGraph.Tree.edgeTowardsOrigin_not_mem_outwardEdgeCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:31.461576+00:00
-- url     : https://prove2.me/submissions/95acade4-575f-4dc2-b76d-c13c10a0679d

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
theorem _root_.solution (v : V) (hdist : 0 < X.dist v₀ v) :
    edgeTowardsOrigin v₀ v hdist ∉ outwardEdgeCone v₀ v := by
  intro hc
  rw [mem_outwardEdgeCone_iff] at hc
  have := edgeTowardsOrigin_target_eq v₀ v hdist
  nth_rw 4 [← this] at hc
  have := source_adj_target v₀ (edgeTowardsOrigin v₀ v hdist)
  apply this.ne
  exact hc.right
end SimpleGraph.Tree
