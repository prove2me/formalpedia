-- Prove2me | solution 1 for SimpleGraph.laplaceSMulHom_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:05:48.028487+00:00
-- url     : https://prove2.me/submissions/aa79d0cb-ce2f-4829-94e0-dc1079ef7f9d

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
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable {V : Type*} [DecidableEq V]
variable (G : Type*) [Group G] [MulAction G V] (X : SimpleGraph V) [GraphAction G X]
attribute [instance] arrowAction
variable {G} {X}
variable [∀ v, Fintype (X.neighborSet v)] (w : V →[G] Rˣ)
namespace SimpleGraph
theorem _root_.solution (htree : X.IsTree) (hdeg : ∀ (v : V), 2 ≤ X.degree v) :
    Function.Surjective (laplaceSMulHom (M := M) (X := X) w) :=
  laplace_surjective htree w hdeg
end SimpleGraph
