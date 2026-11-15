-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_bundleMainProduct_duplicateOutside
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_duplicateOutside
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:37.547816+00:00
-- url     : https://prove2.me/theorems/f222db2a-c01c-4b4a-8035-ba228092ddf0
-- title:
--   The main-density product after outside duplication
-- statement:
--   For any hypergraph bundle $B$, selected vertex set $g_0$, and real base-density function $p$, the main-density product of the bundle duplicated outside $g_0$ is the product of one density for each remaining edge contained in $g_0$ and the square of the density for each remaining edge not contained in $g_0$. Each density is evaluated on the edge image under the bundle projection.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean#L370-L438

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct_duplicateOutside
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by sorry
