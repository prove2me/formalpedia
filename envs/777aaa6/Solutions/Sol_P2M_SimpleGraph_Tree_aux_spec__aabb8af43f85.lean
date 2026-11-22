-- Prove2me | solution 1 for P2M_SimpleGraph_Tree_aux_spec__aabb8af43f85
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:59:58.729197+00:00
-- url     : https://prove2.me/submissions/3678fe42-fce5-45ce-b0a6-b8fa9700deb0

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
variable (n : ℕ) (g : X.edgeSet → M)
namespace SimpleGraph.Tree
theorem _root_.solution (e : X.edgeSet) (n : ℕ) (he : X.dist v₀ (X.target v₀ e) ≤ n)
    (hnotdist : X.distinguishedEdge v₀ (X.source v₀ e)
        (outwardEdgeCone_nonempty_of_source v₀ e) ≠ e) :
    aux w f v₀ n e = 0 := by
  match n with
  | 0 => rw [aux]
  | n + 1 =>
    simp only [aux, dite_eq_left_iff, not_lt]
    split_ifs
    · intro _
      apply solution _ _ _ hnotdist
      assumption
    intro h'
    simp only [auxBorder, Nat.reduceAdd]
    match n with
    | 0 =>
      rw [ite_eq_right_iff]
      intro hc
      contradiction
    | n + 1 =>
      rw [ite_eq_right_iff]
      intro hc
      contradiction
end SimpleGraph.Tree
