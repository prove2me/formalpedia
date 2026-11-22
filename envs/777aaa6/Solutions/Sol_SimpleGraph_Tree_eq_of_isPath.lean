-- Prove2me | solution 1 for SimpleGraph.Tree.eq_of_isPath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:17.894579+00:00
-- url     : https://prove2.me/submissions/00464e7e-5103-477d-a3df-f23466827e86

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
omit [DecidableEq V] [(v : V) → Fintype (X.neighborSet v)]
namespace SimpleGraph.Tree
theorem _root_.solution {x y : V} {p q : X.Walk x y} (hp : p.IsPath) (hq : q.IsPath) :
    p = q := by
  let p' : X.Path x y := ⟨p, hp⟩
  let q' : X.Path x y := ⟨q, hq⟩
  have : p' = q' := X.isTree.IsAcyclic.path_unique _ _
  simpa [p', q'] using this
end SimpleGraph.Tree
