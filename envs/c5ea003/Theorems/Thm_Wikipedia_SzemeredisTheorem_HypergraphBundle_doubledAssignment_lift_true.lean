-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledAssignment_lift_true
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledAssignment_lift_true
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:26.180573+00:00
-- url     : https://prove2.me/theorems/d50ea2d8-4a4a-4bcf-b8dc-850bc93dc17b
-- title:
--   A doubled assignment on the second copy
-- statement:
--   Let $K$ have decidable equality, let $g_0\subseteq K$ be finite, and choose an assignment $y$ on $g_0$ and two outside assignments $(z_0,z_1)$ into a type $G$. At the second lift of any vertex $v$, the doubled assignment equals the ordinary assignment assembled from $y$ and $z_1$, evaluated at $v$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L182-L211

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
theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by sorry
