-- Prove2me | solution 1 for SimpleGraph.Tree.aux_spec_outwardEdgeCone_erase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:55.730327+00:00
-- url     : https://prove2.me/submissions/8085b915-6922-4df3-b2bd-f68c538e1169

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Definitions.Def_BruhatTits_Utils_GraphAction
import Definitions.Def_BruhatTits_Harmonic_Basic
import Theorems.Thm_P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85

set_option autoImplicit false
suppress_compilation
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable {V : Type*} [DecidableEq V]
open BigOperators
open SimpleGraph
open SimpleGraph.Tree
variable {X : SimpleGraph.Tree V} [∀ v, Fintype (X.neighborSet v)] (w : V → Aˣ) (f : V → M)
variable (v₀ : V)
variable (n : ℕ) (g : X.edgeSet → M)
namespace SimpleGraph.Tree
theorem _root_.solution (n : ℕ) (v : V) (hv : X.dist v₀ v + 1 = n)
    (hnonempty : (X.outwardEdgeCone v₀ v).Nonempty) :
    ∑ x ∈ (outwardEdgeCone v₀ v).erase (X.distinguishedEdge v₀ v hnonempty),
    aux w f v₀ n x = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  rw [Finset.mem_erase, ne_eq, mem_outwardEdgeCone_iff] at he
  apply aux_spec₀
  · rw [norm_target_eq_norm_source_add_one, he.right.right]
    omega
  · simp_rw [he.right.right]
    symm
    exact he.left
end SimpleGraph.Tree
