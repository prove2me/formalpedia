-- Prove2me | solution 1 for SimpleGraph.laplace_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:04:41.735994+00:00
-- url     : https://prove2.me/submissions/dcfd9101-3341-4add-ad28-7cb23d38b43d

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_SimpleGraph_Tree_outwardEdgeCone_nonempty_of_two_le_degree
import Theorems.Thm_SimpleGraph_Tree_laplace_preimage

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
namespace SimpleGraph
theorem _root_.solution {X : SimpleGraph V} (htree : IsTree X) [∀ v, Fintype (X.neighborSet v)]
    (w : V → Aˣ) (hmindeg : ∀ v, 2 ≤ X.degree v) : Function.Surjective (X.laplace (M := M) w) := by
  intro f
  let X : SimpleGraph.Tree V := ⟨X, htree⟩
  obtain ⟨v₀⟩ := X.isTree.isConnected.nonempty
  use X.preimage w f v₀
  apply X.laplace_preimage
  intro v
  exact X.outwardEdgeCone_nonempty_of_two_le_degree v₀ (hmindeg v)
end SimpleGraph
