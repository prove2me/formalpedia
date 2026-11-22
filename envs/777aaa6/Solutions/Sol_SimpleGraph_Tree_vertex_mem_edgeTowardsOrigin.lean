-- Prove2me | solution 1 for SimpleGraph.Tree.vertex_mem_edgeTowardsOrigin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:28.57678+00:00
-- url     : https://prove2.me/submissions/32de72bb-7964-4f91-ba49-90cafa75a676

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
omit [(v : V) → Fintype ↑(X.neighborSet v)]
namespace SimpleGraph.Tree
theorem _root_.solution (w : V) (hw : 0 < X.dist v₀ w) :
    w ∈ (edgeTowardsOrigin v₀ w hw).val := by
  nth_rw 2 [← edgeTowardsOrigin_target_eq v₀ w hw]
  exact target_mem v₀ (edgeTowardsOrigin v₀ w hw)
end SimpleGraph.Tree
