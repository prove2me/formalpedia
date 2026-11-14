-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:20.10771+00:00
-- url     : https://prove2.me/theorems/4c0e8f39-5279-4a9f-833f-0be70bbe53c0
-- title:
--   Unit-interval edge weights in a partite simplex system
-- statement:
--   For a weighted partite simplex system $H$, the unit-interval predicate requires
--
--   $$
--   0\le H_j(x)\le1
--   $$
--
--   for every edge colour $j$ and every assignment $x$ on the other vertex parts. The vertex types may be arbitrary; finiteness is not part of this pointwise predicate. This is the boundedness condition used in the later stability estimates for normalized simplex counts.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/SimplexCounting.lean#L17-L20

import Mathlib.Algebra.Order.BigOperators.Expect
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Stable weighted simplex counts

Relative counting will eventually use cut discrepancy and densification.
This file records the elementary endpoint: uniformly close edge weights in
`[0,1]` have close simplex counts.  The proof is the finite telescoping
estimate for products, followed by averaging.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Every edge weight of `H` lies in the unit interval. -/
def EdgeWeightsInUnitInterval {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) : Prop :=
  ∀ j x, 0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1









end Wikipedia.SzemeredisTheorem


