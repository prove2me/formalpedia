-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdge_image_forget_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:10.865968+00:00
-- url     : https://prove2.me/submissions/709b7718-136a-45e3-8e0d-5ba02e3eb24a

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
/-- A doubled edge is stable under lifting after forgetting its vertices. -/
theorem solution
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    have huLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← hwv, ← huw, huLift]
    exact hu
  · intro hv
    have hvLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨doubledVertexForget g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        hvLift⟩
