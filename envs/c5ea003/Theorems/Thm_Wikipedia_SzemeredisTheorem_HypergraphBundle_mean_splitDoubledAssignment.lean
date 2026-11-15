-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitDoubledAssignment
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.mean_splitDoubledAssignment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:04.073953+00:00
-- url     : https://prove2.me/theorems/9d85d257-ce40-4ff1-9b2f-075a2cc6afcf
-- title:
--   Fubini decomposition for doubled assignments
-- statement:
--   Let $K,G$ be finite types, with decidable equality on $K$, and let $g_0\subseteq K$ be finite. For any real-valued function on doubled assignments, its normalized mean equals the iterated mean over one shared assignment on $g_0$ and a pair of independent assignments outside $g_0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L112-L149

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.mean_splitDoubledAssignment
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by sorry
