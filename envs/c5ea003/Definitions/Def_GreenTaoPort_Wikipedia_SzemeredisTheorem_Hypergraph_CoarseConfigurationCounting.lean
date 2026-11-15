-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:07:03.271205+00:00
-- url     : https://prove2.me/theorems/aa04ca68-005d-450a-90eb-b5561fa84a11
-- title:
--   Coarse densities, fine defects, and uniform residuals of atom configurations
-- statement:
--   For a compatible coarse/fine complex and a closed coarse atom configuration, the coarse density of a selected upper atom is its coarse-boundary conditional mean evaluated at the configuration witness. The fine density is the fine-boundary conditional-mean function on the face.
--
--   The defect is the fine density minus that fixed coarse density, and the uniform residual is the selected atom indicator minus the fine density. The boundary indicator selects the coarse immediate-boundary atom containing the witness. A coarse-diagonal construction uses the coarse complex as both endpoints.
--
--   The fully mixed preliminary-regularity predicate requires, at every adjacent rank, regularity of the fine lower boundary against the coarse upper atom family, with the specified rankwise tolerance.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseConfigurationCounting.lean#L22-L259

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
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
# Positive counts for mixed-good coarse configurations

A closed configuration in this file selects atoms of the coarse complex.
The selected coarse upper atom is decomposed using conditional expectation
first on the fine lower boundary and then on the coarse lower boundary.
Thus the main density and defect are exactly those controlled by
`ClosedOrderedAtomConfiguration.IsMixedGood`, while the uniform term is
controlled by regularity of the fine lower boundary against the coarse upper
partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A diagonal pair used only for coarse boundary support -/

/-- Regard the coarse endpoint as both sides of a coarse/fine pair.  This
lets the generic boundary-support lemmas for configuration weights be reused
without introducing a second copy of their combinatorial proof. -/
def OrderedCoarseFineComplex.coarseDiagonal
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    OrderedCoarseFineComplex G k r where
  coarse := P.coarse
  fine := P.coarse
  refines := OrderedPartitionComplex.Refines.refl P.coarse

/-! ## Mixed coarse/fine conditional decomposition -/

/-- Coarse-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationCoarseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.coarse e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    (orderedFaceTuple e.face A.witness)

/-- Fine-boundary conditional density of the selected coarse upper atom. -/
noncomputable def mixedConfigurationFineDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  orderedBoundaryStructured
    (positiveFaceLowerLayer P.fine e)
    e.face
    (partitionAtomIndicator
      (P.coarse.partition e.lowerRank.succ e.face)
      (A.atom e.lowerRank.succ e.face))
    y

/-- Fine-boundary density minus the coarse-boundary density selected by the
configuration witness. -/
noncomputable def mixedConfigurationDefect
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  mixedConfigurationFineDensity P A e y -
    mixedConfigurationCoarseDensity P A e

/-- Residual of a coarse upper atom after conditioning on the fine lower
boundary. -/
noncomputable def mixedConfigurationUniform
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  configurationFaceWeight A e y -
    mixedConfigurationFineDensity P A e y

/-- Indicator of the canonical coarse boundary atom determined by the
coarse configuration witness. -/
noncomputable def mixedConfigurationBoundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (orderedBoundaryPartition
      (positiveFaceLowerLayer P.coarse e) e.face)
    (orderedBoundaryAtomAt
      (positiveFaceLowerLayer P.coarse e) e.face
      (orderedFaceTuple e.face A.witness))
    y











/-! ## Coarse boundary support and selected-face decomposition -/







/-! ## Mixed coarse-upper regularity and the uniform contribution -/

/-- At every rank, the fine lower boundary is regular against the coarse
upper atom family. -/
def IsFullyMixedPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (τ : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (P.fine.partition j.castSucc)
      (P.coarse.partition j.succ)
      (τ j)













/-! ## Localized mixed defect contribution -/











/-! ## One-face recurrence -/





/-! ## Rank-dependent totalized recurrence -/











/-! ## Rankwise full-count lower bounds -/





/-! ## Fine-regular complexity corollaries -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.coarseDiagonal.eq_1,
    `Wikipedia.SzemeredisTheorem.mixedConfigurationBoundaryIndicator.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


