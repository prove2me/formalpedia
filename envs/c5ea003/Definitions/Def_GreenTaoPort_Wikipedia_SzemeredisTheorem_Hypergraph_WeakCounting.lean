-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:58:15.879206+00:00
-- url     : https://prove2.me/theorems/77154a81-9d3a-4306-ba69-25a68ad1a88b
-- title:
--   Canonical face coordinates for mixed simplex cut tests
-- statement:
--   A deleted coordinate vector is reindexed by the increasing enumeration of the remaining coordinates, giving a canonical tuple of length $n$. This also reexpresses each simplex edge weight as a real function on that tuple space.
--
--   In an edge-by-edge comparison of systems $H$ and $K$, the non-distinguished factor uses $H$ before the selected colour and $K$ after it. The bundle supplies insertion into an erased-coordinate tuple and the resulting cut-test family after fixing the distinguished vertex. These definitions give the precise coordinate representation needed to apply weak face regularity to a mixed simplex term.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/WeakCounting.lean#L23-L184

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
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
# Weak-regularity counting for simplex systems

Each deleted face of a simplex with `n+1` colours is canonically presented as
an ordinary `Fin n → G` tuple.  A family of regularity states therefore gives
a structured simplex system by conditionally averaging every edge weight.

The main result is an exact weak counting lemma.  If every edge residual is
small against lower-face product cuts, then the original and structured
simplex counts differ by at most `(n+1) ε`.  The proof fixes the missing
vertex in one telescoping term; the remaining edge factors become precisely a
bounded cut-test family on the distinguished edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Canonical `Fin n` presentation of a dependent deleted-coordinate
vector. -/
noncomputable def deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)







/-- Reparameterize one edge weight by the canonical `Fin n` face tuple. -/
noncomputable def canonicalEdgeFunction
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)













/-- The non-distinguished factors in an ordered simplex telescoping term. -/
def orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j i : Fin k) (x : Fin k → G) : ℝ :=
  (if i < j then H.edgeWeight i (deleteCoordinate x i) else 1) *
  (if j < i then K.edgeWeight i (deleteCoordinate x i) else 1)



/-- Insert the omitted coordinate into a tuple presented with the
subtraction-based arity used by `eraseCoordinate`. -/
def insertErasedCoordinate
    {G : Type*} {n : ℕ} (t : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    Fin n → G := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => exact Fin.insertNth t a z



/-- After fixing the distinguished vertex, the other edge of colour
`j.succAbove t` is a function omitting face coordinate `t`. -/
def simplexMixedCutTest
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G) :
    CutTestFamily G n :=
  fun t z =>
    orderedSimplexEdgeFactor H K j (j.succAbove t)
      (Fin.insertNth j a (insertErasedCoordinate t a z))





















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.canonicalEdgeFunction.eq_1,
    `Wikipedia.SzemeredisTheorem.deletedFaceTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.orderedSimplexEdgeFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.simplexMixedCutTest.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


