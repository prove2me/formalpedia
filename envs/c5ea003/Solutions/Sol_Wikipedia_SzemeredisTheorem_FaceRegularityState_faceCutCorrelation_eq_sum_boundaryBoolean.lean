-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.FaceRegularityState.faceCutCorrelation_eq_sum_boundaryBoolean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:30.705242+00:00
-- url     : https://prove2.me/submissions/2c01bf7b-5381-4867-8ae9-f219cf381e8d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_FaceRegularityState_faceCutCorrelation_eq_sum_boolean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_booleanFaceCutSupport_eval

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section



/-!
# Weak regularity against lower-face cut tests

For a function on `Fin r → G`, the hypergraph cut tests are products of
`r` functions, with the `i`th factor omitting coordinate `i`.  A Boolean
cut-test family has a support in the full tuple space.  This file connects
those supports to the abstract energy-increment machinery and proves a
genuine finite weak-regularity lemma:

* the output refines the input partition;
* its complexity grows by an ambient-size-independent power of two;
* the residual is small against every `[0,1]`-valued lower-face cut test.

The passage from Boolean to bounded tests is an exact finite Bernoulli
mixture, not an approximation.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem mem_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    x ∈ booleanFaceCutSupport b ↔
      ∀ i, b ⟨i, eraseCoordinate i x⟩ = true := by
  simp [booleanFaceCutSupport]











namespace FaceRegularityState



/-- On Boolean tests, face-cut correlation is the existing Boolean support
correlation used by the energy increment. -/
theorem faceCutCorrelation_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ)
    (b : BooleanCutAssignment G r) :
    S.faceCutCorrelation f
        (cutTestFamilyOfBooleanAssignment b) =
      S.booleanCutCorrelation f (booleanFaceCutSupport b) := by
  unfold faceCutCorrelation booleanCutCorrelation
  apply congrArg mean
  funext x
  rw [booleanFaceCutSupport_eval]













end FaceRegularityState

end Wikipedia.SzemeredisTheorem

end

section


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











@[simp]
theorem booleanAssignmentOfBoundary_equiv_apply
    {G : Type*} {j : ℕ}
    (b : BooleanCutAssignment G (j + 1)) :
    booleanAssignmentOfBoundary
        ((booleanBoundaryAssignmentEquiv G j) b) = b :=
  booleanAssignmentOfBoundary_ofBoolean b









/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl

/-- The boundary support of a curried assignment is the ordinary Boolean
face-cut support of its uncurried assignment. -/
theorem boundaryBooleanCutSupport_eq_booleanFaceCutSupport
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (b : BoundaryBooleanCutAssignment G j) :
    boundaryBooleanCutSupport b =
      booleanFaceCutSupport (booleanAssignmentOfBoundary b) := by
  classical
  ext x
  rw [mem_boundaryBooleanCutSupport,
    mem_booleanFaceCutSupport]
  simp only [booleanAssignmentOfBoundary,
    eraseBoundaryCoordinate_eq_eraseCoordinate]







namespace FaceRegularityState





end FaceRegularityState





end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.FaceRegularityState

open Wikipedia.SzemeredisTheorem.FaceRegularityState in
/-- Exact convex-mixture formula for residual correlation against a bounded
boundary product.  The identity itself does not require boundedness. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {j : ℕ}
    (S : FaceRegularityState (Fin (j + 1) → G))
    (f : (Fin (j + 1) → G) → ℝ)
    (u : CutTestFamily G (j + 1)) :
    S.faceCutCorrelation f u =
      ∑ b : BoundaryBooleanCutAssignment G j,
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b) := by
  classical
  rw [S.faceCutCorrelation_eq_sum_boolean]
  exact
    Fintype.sum_equiv
      (booleanBoundaryAssignmentEquiv G j)
      (fun b : BooleanCutAssignment G (j + 1) =>
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b))
      (fun b : BoundaryBooleanCutAssignment G j =>
        boundaryBernoulliWeight u b *
          S.booleanCutCorrelation f
            (boundaryBooleanCutSupport b))
      (fun b => by
        dsimp only
        rw [S.faceCutCorrelation_boolean]
        simp [boundaryBernoulliWeight,
          boundaryBooleanCutSupport_eq_booleanFaceCutSupport])
