-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_image_true_sdiff_image_false
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.image_true_sdiff_image_false
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:32:59.15041+00:00
-- url     : https://prove2.me/theorems/80e455dd-4d14-4570-96b2-fe979f7411d9
-- title:
--   The difference of the two doubled edge images
-- statement:
--   Let $g_0$ be a finite vertex set and $s$ a finite family of finite vertex sets. The second-copy image of $s$ minus its first-copy image consists exactly of second-copy images of those $g\in s$ that are not contained in $g_0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean#L308-L353

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.image_true_sdiff_image_false
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by sorry
