-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_duplicateOutside_closed
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.duplicateOutside_closed
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:00.149051+00:00
-- url     : https://prove2.me/theorems/c7569892-f3f7-4f8a-b00d-a4ecd8ca04a0
-- title:
--   Outside duplication preserves closure after edge erasure
-- statement:
--   For any hypergraph bundle $B$ and finite vertex set $g_0$, if erasing $g_0$ leaves a bundle closed under inclusion, then the bundle duplicated outside $g_0$ is also closed under inclusion.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L739-L768

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.duplicateOutside_closed
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by sorry
