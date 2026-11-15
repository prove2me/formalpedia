-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.image_forget_doubledEdge
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:44.417911+00:00
-- url     : https://prove2.me/submissions/8b014ee1-8048-4034-988e-eba13f0c7242

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
/-- Forgetting a lifted edge recovers the original edge. -/
@[simp]
theorem solution
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩
