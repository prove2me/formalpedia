-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_image_forget_doubledEdge
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.image_forget_doubledEdge
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:03.427686+00:00
-- url     : https://prove2.me/theorems/2560051c-10ef-4424-aa23-2601bee21ab7
-- title:
--   Forgetting a doubled edge recovers its source
-- statement:
--   For finite vertex sets $g_0,g$ in a type with decidable equality and either Boolean copy, the image of the doubled edge of $g$ under the vertex-forgetting map is exactly $g$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L226-L245

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

@[simp]
theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by sorry
