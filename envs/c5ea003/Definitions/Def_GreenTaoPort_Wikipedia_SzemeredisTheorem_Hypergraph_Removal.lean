-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:52:46.840205+00:00
-- url     : https://prove2.me/theorems/8429f075-5ff3-4f3f-b090-4d3ab6b9253c
-- title:
--   Coloured face-deletion families and normalized costs
-- statement:
--   For a partite simplex, a deletion family chooses one finite set of deleted faces for every colour. The total deletion count is the sum of their cardinalities. When the vertex parts are finite, the deletion capacity is the sum of the cardinalities of all available coloured face spaces.
--
--   The colourwise deletion density divides a chosen colour's deletion count by its face-space cardinality. The normalized total cost divides the total deletion count by the total capacity. Both are total real-valued quantities under the convention that division by zero is zero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Removal.lean#L24-L375

import Mathlib.Data.Finset.Max
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Partition.Finpartition
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Finite deletion framework for simplex removal

This file supplies the finite combinatorial interface surrounding the deep
hypergraph-removal argument.  A deletion family consists of one finite set of
deleted faces for each colour.  We construct the surviving hypergraph, prove
that covers are exactly the deletion families with no surviving simplex, and
develop monotonicity, cost normalization, trimming, canonical covers, and
existence of a minimum finite cover.

No quantitative hypergraph-removal theorem is asserted here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace SimplexHypergraph

/-- One finite set of deleted faces for each edge colour. -/
abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)















































/-- Total number of deleted coloured faces. -/
def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card













/-- Total number of available coloured face slots. -/
def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)







/-- Density of the deleted faces in one colour class. -/
noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)







/-- Deleted-face density among all coloured face slots.  If the capacity is
zero, Lean's field division convention makes the value zero. -/
noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)















end SimplexHypergraph









end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.colorDeletionDensity.eq_1,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.deletionCapacity.eq_1,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.deletionCount.eq_1,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.normalizedDeletionCost.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


