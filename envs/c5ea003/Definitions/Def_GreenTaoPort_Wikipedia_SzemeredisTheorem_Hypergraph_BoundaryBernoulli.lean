-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:04:14.223257+00:00
-- url     : https://prove2.me/theorems/d5a060e2-bfc0-49ab-9721-6167de7aad99
-- title:
--   Boolean boundary coordinates and bounded preliminary regularity
-- statement:
--   Boolean cut assignments on a successor-arity face can be presented either as functions on the ordinary cut-coordinate type or as a family indexed first by the omitted coordinate and then by the remaining tuple. The bundle provides the explicit currying and uncurrying maps, their inverse certificates, and the resulting equivalence.
--
--   The boundary Bernoulli weight is the existing product Bernoulli coefficient transported through this equivalence. The bounded preliminary-regularity predicate requires every upper-face atom indicator to be face-cut regular against the partition induced by the shared lower boundary. Its tests range over bounded boundary products, rather than only Boolean products.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/BoundaryBernoulli.lean#L30-L347

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Curry an ordinary Boolean cut assignment at successor arity into the
boundary-assignment presentation. -/
def boundaryBooleanAssignmentOfBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    BoundaryBooleanCutAssignment G j :=
  fun i z => b ⟨i, z⟩

/-- Uncurry a boundary Boolean assignment into the ordinary cut-coordinate
presentation. -/
def booleanAssignmentOfBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    BooleanCutAssignment G (j + 1) :=
  fun q => b q.1 q.2

@[simp]
theorem booleanAssignmentOfBoundary_ofBoolean
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        (boundaryBooleanAssignmentOfBoolean b) = b := by
  funext q
  cases q
  rfl

@[simp]
theorem boundaryBooleanAssignmentOfBoolean_ofBoundary
    {G : Type*} {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanAssignmentOfBoolean
        (booleanAssignmentOfBoundary b) = b := by
  funext i z
  rfl

/-- The curried and uncurried Boolean boundary assignments are equivalent. -/
def booleanBoundaryAssignmentEquiv
    (G : Type*) (j : ℕ) :
    BooleanCutAssignment G (j + 1) ≃
      BoundaryBooleanCutAssignment G j where
  toFun := boundaryBooleanAssignmentOfBoolean
  invFun := booleanAssignmentOfBoundary
  left_inv := booleanAssignmentOfBoundary_ofBoolean
  right_inv := boundaryBooleanAssignmentOfBoolean_ofBoundary



/-- The Bernoulli coefficient of one boundary Boolean assignment. -/
def boundaryBernoulliWeight
    {G : Type*} [Fintype G] {j : ℕ}
    (u : CutTestFamily G (j + 1))
    (b : BoundaryBooleanCutAssignment G j) : ℝ :=
  bernoulliAssignmentWeight
    (cutTestCoordinateValue u)
    (booleanAssignmentOfBoundary b)

















namespace FaceRegularityState





end FaceRegularityState

/-- Preliminary ordered regularity tested against every bounded boundary
product rather than only Boolean boundary products. -/
def IsPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) : Prop :=
  ∀ (e : OrderedFace k (j + 1))
      (a : (upper e).parts),
    (⟨orderedBoundaryPartition lower e⟩ :
      FaceRegularityState (Fin (j + 1) → G)).IsFaceCutRegular
        (partitionAtomIndicator (upper e) a) ε



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.booleanAssignmentOfBoundary.eq_1,
    `Wikipedia.SzemeredisTheorem.boundaryBernoulliWeight.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


