-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:33.252598+00:00
-- url     : https://prove2.me/theorems/41196199-2bf6-4cde-876a-c60287a5d751
-- title:
--   Unweighted partite simplex hypergraphs and deletion covers
-- statement:
--   For vertex types $(V_i)_{i<k}$, an unweighted partite simplex hypergraph specifies, for each colour $j<k$, a predicate on assignments to all parts other than $j$. A labelled simplex is a full assignment whose deletion at every coordinate satisfies the corresponding edge predicate.
--
--   When the vertex types are finite, all labelled simplices form a finite set. The associated weighted system uses the zero–one indicator of each edge predicate. A family of deleted edge sets is a simplex cover if every labelled simplex has at least one colour whose deleted-coordinate assignment lies in the chosen deleted set. The bundle includes the exact membership characterization for the finite simplex set.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/Unweighted.lean#L16-L148

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Unweighted partite simplex hypergraphs

The removal argument uses a `(k - 1)`-uniform, `k`-partite hypergraph whose
edge of colour `j` depends on every vertex coordinate except `j`.  This file
gives the finite predicate-valued interface and connects its labelled
simplices exactly to the weighted counting API.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- An unweighted `(k - 1)`-uniform, `k`-partite hypergraph. -/
structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph





/-- The finite set of labelled simplices. -/
noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

/-- Regard an unweighted hypergraph as a zero-one weighted system. -/
noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }













/-- A family of deleted edge sets meets every labelled simplex. -/
def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j



end SimplexHypergraph

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.ctorIdx,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.mk.inj,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.mk.injEq,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.noConfusionType,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.simplexFinset.eq_1,
    `Wikipedia.SzemeredisTheorem.SimplexHypergraph.toWeighted.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


