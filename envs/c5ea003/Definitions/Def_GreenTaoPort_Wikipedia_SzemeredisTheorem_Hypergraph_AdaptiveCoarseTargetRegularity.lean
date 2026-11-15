-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:09:48.87737+00:00
-- url     : https://prove2.me/theorems/f3721e17-2d5b-4123-8318-2c22460541e8
-- title:
--   Adaptive top-down schedule trees and their realizations
-- statement:
--   An adaptive schedule is a finite tree indexed by its remaining rank height. Each nonterminal node carries a real tolerance sequence, a natural budget sequence, a finite horizon, and one subtree for each possible selected index. Thus a lower-rank schedule may depend on all indices previously selected at higher ranks.
--
--   Admissibility imposes the local nonnegative-tolerance and strict energy-budget conditions, a positive horizon, and admissibility of every subtree. A landing is a root-to-leaf sequence of index choices. Its tolerances, budgets, horizons, and indices are flattened into bottom-up rank order.
--
--   A realization pairs such a landing with an ordinary coarse-target regularity certificate whose selected indices agree exactly with the landing. This equality ensures that each lower-rank schedule is the subtree determined by the earlier higher-rank selections.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/AdaptiveCoarseTargetRegularity.lean#L22-L341

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Adaptive top-down coarse-target regularity

The fixed-vector coarse-target theorem chooses one tower index at every
rank, but fixes all tower lengths before any of those choices are known.
For the removal argument this is unnecessarily rigid: after the top-rank
index has been selected, the horizon at the next rank may be chosen as a
function of that index, and so on.

This file packages such data as a finite decision tree.  A node contains
the tolerance, budget, and horizon for the current (highest remaining)
rank, together with one subtree for every admissible index.  Thus a branch
is genuinely path dependent.  A landing is a root-to-leaf branch.  Its
data are flattened in the bottom-up rank order used by
`CoarseTargetOrderedComplexRegularityCertificate`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A finite tree of top-down regularity schedules.

At a node of height `r + 1`, the displayed schedule is used at rank `r`.
After an index `i : Fin length` is selected, `next i` is the schedule for
the remaining ranks.  In particular, every later horizon may depend on all
earlier selected indices. -/
inductive AdaptiveCoarseTargetSchedule (k : ℕ) : ℕ → Type
  | nil : AdaptiveCoarseTargetSchedule k 0
  | node {r : ℕ}
      (tolerance : ℕ → ℝ)
      (budget : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → AdaptiveCoarseTargetSchedule k r) :
      AdaptiveCoarseTargetSchedule k (r + 1)

namespace AdaptiveCoarseTargetSchedule

/-- The local energy-increment hypotheses hold at every node of an
adaptive schedule tree. -/
def IsAdmissible {k r : ℕ} :
    AdaptiveCoarseTargetSchedule k r → Prop
  | .nil => True
  | .node tolerance budget length next =>
      (∀ n, 0 ≤ tolerance n) ∧
      (∀ n,
        (Fintype.card (OrderedFace k r) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible

/-- A root-to-leaf landing in an adaptive schedule tree. -/
inductive Landing {k : ℕ} :
    {r : ℕ} → AdaptiveCoarseTargetSchedule k r → Type
  | nil : Landing (.nil : AdaptiveCoarseTargetSchedule k 0)
  | node {r : ℕ}
      {tolerance : ℕ → ℝ}
      {budget : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → AdaptiveCoarseTargetSchedule k r}
      (index : Fin length)
      (lower : Landing (next index)) :
      Landing (.node tolerance budget length next)

namespace Landing

/-- Flatten the tolerances along a landing into bottom-up rank order. -/
def tolerance {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (tolerance := tolerance) _ lower =>
      fun j => Fin.lastCases tolerance lower.tolerance j

/-- Flatten the tower budgets along a landing into bottom-up rank order. -/
def budget {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (budget := budget) _ lower =>
      fun j => Fin.lastCases budget lower.budget j

/-- Flatten the tower horizons along a landing into bottom-up rank order. -/
def length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j

/-- Flatten the selected indices along a landing into bottom-up rank order. -/
def index {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node chosen lower =>
      fun j => Fin.lastCases chosen.1 lower.index j

@[simp]
theorem tolerance_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance (Fin.last r) =
      tolerance := by
  simp [Landing.tolerance]

@[simp]
theorem tolerance_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j.castSucc =
      lower.tolerance j := by
  simp [Landing.tolerance]

@[simp]
theorem budget_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget (Fin.last r) =
      budget := by
  simp [Landing.budget]

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

@[simp]
theorem length_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length (Fin.last r) =
      length := by
  simp [Landing.length]

@[simp]
theorem length_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j.castSucc =
      lower.length j := by
  simp [Landing.length]

@[simp]
theorem index_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index (Fin.last r) =
      chosen.1 := by
  simp [Landing.index]

@[simp]
theorem index_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index j.castSucc =
      lower.index j := by
  simp [Landing.index]









end Landing

/-- A realization of an adaptive schedule is a landing together with an
ordinary coarse-target certificate whose actual selected indices are
exactly the indices of that landing.  Consequently the flattened schedule
used at every lower rank is the subtree chosen by the earlier, higher-rank
certificate indices. -/
structure Realization
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r) where
  landing : S.Landing
  certificate :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial
        landing.tolerance landing.budget landing.length
  index_eq : certificate.index = landing.index





end AdaptiveCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.IsAdmissible.match_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.brecOn.eq,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.brecOn.go,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.budget.eq_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.budget.eq_2,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.budget.eq_def,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.ctorElimType,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.ctorIdx,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.index.eq_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.index.eq_2,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.index.eq_def,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.length.eq_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.length.eq_2,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.length.eq_def,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.nil.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.noConfusionType,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.node.inj,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.node.injEq,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.node.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.tolerance.eq_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.tolerance.eq_2,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.tolerance.eq_def,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Landing.tolerance.match_1,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.ctorIdx,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.mk.inj,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.mk.injEq,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.Realization.noConfusionType,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.brecOn.eq,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.brecOn.go,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.ctorElimType,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.ctorIdx,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.nil.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.noConfusionType,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.node.inj,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.node.injEq,
    `Wikipedia.SzemeredisTheorem.AdaptiveCoarseTargetSchedule.node.sizeOf_spec
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


