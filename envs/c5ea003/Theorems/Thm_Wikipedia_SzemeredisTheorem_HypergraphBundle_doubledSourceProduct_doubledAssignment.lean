-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledSourceProduct_doubledAssignment
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_doubledAssignment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:32:56.037086+00:00
-- url     : https://prove2.me/theorems/c58f8bc5-282f-44f0-849a-3872140e9401
-- title:
--   The doubled source product splits into two remainder fibers
-- statement:
--   For a hypergraph bundle $B$, finite vertex set $g_0$, arbitrary real edge weights $A$, assignment $y$ on $g_0$, and two outside assignments $z_0,z_1$, the doubled source product on the assembled doubled assignment equals the product of the two edge-remainder fibers at $(y,z_0)$ and $(y,z_1)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleDuplication.lean#L333-L406

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledSourceProduct_doubledAssignment
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by sorry
