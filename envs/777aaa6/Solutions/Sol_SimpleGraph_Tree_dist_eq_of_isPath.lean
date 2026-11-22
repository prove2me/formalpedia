-- Prove2me | solution 1 for SimpleGraph.Tree.dist_eq_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:54.125617+00:00
-- url     : https://prove2.me/submissions/eff089fd-dc6a-45b4-b7e2-7857e2fcef5f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_eq_of_isPath

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
theorem _root_.solution {x y : V} (p : X.Walk x y) (hp : p.IsPath) :
    X.dist x y = p.length := by
  obtain ⟨q, hq, hqlen⟩ := X.isTree.isConnected.exists_path_of_dist x y
  have : p = q := eq_of_isPath hp hq
  rw [eq_of_isPath hp hq, hqlen]
end SimpleGraph.Tree
