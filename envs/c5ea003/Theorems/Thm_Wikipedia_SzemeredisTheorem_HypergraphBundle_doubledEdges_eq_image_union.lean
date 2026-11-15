-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_doubledEdges_eq_image_union
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdges_eq_image_union
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:29:43.8492+00:00
-- url     : https://prove2.me/theorems/525c10c5-2930-4db3-9c53-a2c4725d4c59
-- title:
--   The doubled edge family is a union of two images
-- statement:
--   For any hypergraph bundle $B$ and finite vertex set $g_0$, the doubled edge family relative to $g_0$ is the union of the first-copy and second-copy images of $B.\mathrm{edges}\setminus\{g_0\}$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean#L280-L306

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Edge-filtered subbundles -/
/-! ## The lower-order and strict-boundary filtrations -/
/-! ## Main-density products -/
/-! ## The main product under duplication -/

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.doubledEdges_eq_image_union
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by sorry
