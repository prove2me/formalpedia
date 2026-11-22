-- Prove2me | solution 1 for SimpleGraph.Tree.mem_outwardCone_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:58:55.450033+00:00
-- url     : https://prove2.me/submissions/b8dd86e0-7782-4b88-a765-38e22f73e6da

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
omit [DecidableEq V]
namespace SimpleGraph.Tree
theorem _root_.solution (w a : V) :
    a ∈ X.outwardCone v₀ w ↔ (X.Adj w a ∧ X.dist v₀ w < X.dist v₀ a) := by
  simp [outwardCone]
end SimpleGraph.Tree
