-- Prove2me | solution 1 for SimpleGraph.laplaceHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:05:47.564701+00:00
-- url     : https://prove2.me/submissions/db87ba32-baf0-487b-b711-fe5f75c4f156

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_laplace_surjective

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
variable {X : SimpleGraph V}
variable [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ)
namespace SimpleGraph
theorem _root_.solution (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (X.laplaceHom (M := M) w) :=
  laplace_surjective htree w hdeg
end SimpleGraph
