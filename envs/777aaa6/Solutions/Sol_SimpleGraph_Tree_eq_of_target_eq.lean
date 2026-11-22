-- Prove2me | solution 1 for SimpleGraph.Tree.eq_of_target_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:27.120318+00:00
-- url     : https://prove2.me/submissions/24effea4-2f70-4c6d-bf11-a0d648bb85b6

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_source_eq_of_target_eq

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
theorem _root_.solution (e f : X.edgeSet) (h : X.target v₀ e = X.target v₀ f) : e = f := by
  ext : 1
  rw [edge_eq_mk_source_target v₀, edge_eq_mk_source_target v₀, h, source_eq_of_target_eq v₀ e f h]
end SimpleGraph.Tree
