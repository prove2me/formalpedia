-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mixedSimplexTerm_insertNth_eq_faceCutDifference
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:56:54.088974+00:00
-- url     : https://prove2.me/submissions/48d67b2a-7ed3-424f-a9ae-153c42b7cce9

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
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
import Mathlib.Algebra.Order.Chebyshev
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_prod_simplexMixedCutTest_eraseCoordinate

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
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl







/-- Deleting coordinate `j` from a full tuple agrees with the canonical
`Fin n` presentation of the remaining coordinates. -/
theorem deleteCoordinate_eq_finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1)) (x : Fin (n + 1) → G) :
    deleteCoordinate x j =
      finTupleToDeletedVector j
        (fun t => x (j.succAbove t)) := by
  funext i
  change x i.1 =
    x (j.succAbove ((finSuccAboveEquiv j).symm i))
  apply congrArg x
  have hi :=
    congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply i)
  exact hi.symm







end Wikipedia.SzemeredisTheorem

end
/-!
# Cut-discrepancy comparison of bounded relative simplex states

For an arbitrary simplex edge, the natural discrepancy is tested directly
on its deleted-face coordinates against products of functions omitting one
face coordinate.  This is the same cut-test family used by
`FaceRegularityState.IsFaceCutRegular`, but here it compares two arbitrary
edge functions rather than a function and its conditional expectation.

The existing `simplexMixedCutTest` reconstructs the product of all
non-distinguished factors in an edge-by-edge telescoping term.  Consequently
face-cut discrepancy controls each mixed correlation whenever both simplex
systems are fully bounded.  Summing the correlations gives an actual
weighted-simplex comparison theorem with loss one `ε` per colour.

The final section specializes this comparison to the arbitrary whole-face
functions produced by recursive projection and re-embedding.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Direct face-cut discrepancy -/
/-! ## Edgewise discrepancy for arbitrary weighted simplices -/

open Wikipedia.SzemeredisTheorem in
/-- Fixing the distinguished simplex coordinate turns its mixed
telescoping term into the direct face residual paired with the reconstructed
bounded cut product. -/
theorem solution
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (a : G) (y : Fin n → G) :
    mixedSimplexTerm H K j (Fin.insertNth j a y) =
      (canonicalEdgeFunction H j y -
        canonicalEdgeFunction K j y) *
      cutTestProduct (simplexMixedCutTest H K j a) y := by
  have hHj :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction H j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  have hKj :
      K.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction K j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  unfold mixedSimplexTerm
  rw [hHj, hKj]
  rw [show
      cutTestProduct (simplexMixedCutTest H K j a) y =
        (∏ i ∈ (Finset.univ :
            Finset (Fin (n + 1))) with i < j,
          H.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i)) *
        ∏ i ∈ (Finset.univ :
            Finset (Fin (n + 1))) with j < i,
          K.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i) by
      exact prod_simplexMixedCutTest_eraseCoordinate
        H K j a y]
  ring
