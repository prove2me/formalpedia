-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdge_false_ne_true_of_mem_complement
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdge_false_ne_true_of_mem_complement
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:24.666629+00:00
-- url     : https://prove2.me/theorems/29c5d719-6137-453b-a388-07150cc02de5
-- title:
--   An outside vertex distinguishes the two doubled edges
-- statement:
--   For finite vertex sets $g_0,g$ in a type with decidable equality, if $g$ contains a vertex outside $g_0$, its first and second doubled edges relative to $g_0$ are distinct.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L269-L289

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdge_false_ne_true_of_mem_complement
    (g₀ : Finset K) {g : Finset K}
    {v : K} (hvg : v ∈ g) (hvoutside : v ∉ g₀) :
    doubledEdge g₀ false g ≠
      doubledEdge g₀ true g := by sorry
