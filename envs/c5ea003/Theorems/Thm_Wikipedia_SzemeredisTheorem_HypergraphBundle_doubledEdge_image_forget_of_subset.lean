-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdge_image_forget_of_subset
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdge_image_forget_of_subset
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:27.071877+00:00
-- url     : https://prove2.me/theorems/11255dc4-3805-479e-a2fe-79845eace753
-- title:
--   Forgetting and relifting a subset of one doubled edge
-- statement:
--   Let $g_0,g$ be finite vertex sets and choose either Boolean copy. If $d$ is a subset of the corresponding doubled edge of $g$, then forgetting the doubled tags on $d$ and lifting the resulting vertex set back into the same copy recovers exactly $d$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L705-L737

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdge_image_forget_of_subset
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by sorry
