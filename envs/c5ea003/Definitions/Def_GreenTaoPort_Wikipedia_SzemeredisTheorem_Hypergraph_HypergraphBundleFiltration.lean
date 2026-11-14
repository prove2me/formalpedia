-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:08.264549+00:00
-- url     : https://prove2.me/theorems/eb8eaf0e-9c7e-4a23-9ba2-fe25a2f7a23b
-- title:
--   Filtering occurrence edges and forming bundle boundary products
-- statement:
--   An occurrence-edge predicate filters a hypergraph bundle's finite edge set while preserving its projection to the base hypergraph and its edgewise projection certificates. Two special filters retain edges of cardinality below a natural rank, or proper subsets of a distinguished occurrence set.
--
--   Given a real density assigned to each base edge, the bundle main product multiplies those densities over the projected occurrence edges, with one factor for every occurrence edge. Repeated projected base edges therefore contribute repeated factors. The included membership support identifies the filtered edge condition exactly.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFiltration.lean#L30-L210

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Lean
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/

/-- Retain exactly the occurrence edges satisfying `P`. -/
def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1



@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]









/-! ## The lower-order and strict-boundary filtrations -/

/-- The subbundle consisting of edges whose cardinality is strictly below
`d`. -/
def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d













/-- The strict-boundary subbundle below `g₀`. -/
def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀



@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]









/-! ## Main-density products -/

/-- Product of a base density over all occurrence edges of a bundle. -/
noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)











/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.bundleMainProduct.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.filterEdges.congr_simp,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.filterEdges.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.lowerOrder.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.strictBoundary.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


