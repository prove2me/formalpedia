-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledAssignment_lift_false
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:03:38.168727+00:00
-- url     : https://prove2.me/submissions/63b734aa-400f-41f2-ae3e-654a6d704ffe

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- On the first copy, a doubled assignment agrees with the ordinary
assignment assembled from the shared tuple and first outside tuple. -/
@[simp]
theorem solution
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1
