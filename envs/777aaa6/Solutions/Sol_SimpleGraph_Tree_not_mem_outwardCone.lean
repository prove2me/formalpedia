-- Prove2me | solution 1 for SimpleGraph.Tree.not_mem_outwardCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:01:45.069641+00:00
-- url     : https://prove2.me/submissions/ec505737-670e-43ed-b1ce-733dca5ae899

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_mem_outwardCone_iff

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
theorem _root_.solution (w : V) : w ∉ X.outwardCone v₀ w := by
  simp [mem_outwardCone_iff]
end SimpleGraph.Tree
