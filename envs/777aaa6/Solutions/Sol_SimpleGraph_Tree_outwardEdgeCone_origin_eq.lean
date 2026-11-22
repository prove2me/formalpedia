-- Prove2me | solution 1 for SimpleGraph.Tree.outwardEdgeCone_origin_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:11.483579+00:00
-- url     : https://prove2.me/submissions/c2b90735-ce26-4867-992e-bebee2e9d73c

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
theorem _root_.solution : X.outwardEdgeCone v₀ v₀ = X.incidenceFinset' v₀ := by
  ext e
  simp only [mem_outwardEdgeCone_iff, mem_incidenceFinset', and_iff_left_iff_imp]
  intro h
  exact source_eq_origin_of_mem v₀ e h
end SimpleGraph.Tree
