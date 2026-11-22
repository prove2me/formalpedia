-- Prove2me | solution 1 for SimpleGraph.Tree.eq_edgeTowardsOrigin_iff_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:02:01.762183+00:00
-- url     : https://prove2.me/submissions/cf95cb6f-1a79-4a6b-b24a-0a71e9a16b48

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
omit [(v : V) → Fintype ↑(X.neighborSet v)]
namespace SimpleGraph.Tree
theorem _root_.solution (w : V) (hw : 0 < X.dist v₀ w) (e : X.edgeSet)
    (hmem : w ∈ e.val) :
    e = X.edgeTowardsOrigin v₀ w hw ↔ X.target v₀ e = w := by
  constructor
  · rintro rfl
    apply edgeTowardsOrigin_target_eq
  · intro h
    apply eq_of_target_eq v₀
    simpa
end SimpleGraph.Tree
