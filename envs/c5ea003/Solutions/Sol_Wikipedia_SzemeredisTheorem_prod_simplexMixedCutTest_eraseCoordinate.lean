-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.prod_simplexMixedCutTest_eraseCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:30:15.045196+00:00
-- url     : https://prove2.me/submissions/2e5bcdff-e52f-4bb2-b980-6e073428e702

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
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
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





/-- Replacing a coordinate does not change the deleted vector at that
coordinate. -/
@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

/-- Inserting a replacement into the erased tuple is `Function.update`. -/
theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x



























end Wikipedia.SzemeredisTheorem

end

section




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

























@[simp]
theorem orderedSimplexEdgeFactor_self
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    orderedSimplexEdgeFactor H K j j x = 1 := by
  simp [orderedSimplexEdgeFactor]



@[simp]
theorem insertErasedCoordinate_eraseCoordinate
    {G : Type*} {n : ℕ}
    (t : Fin n) (a : G) (y : Fin n → G) :
    insertErasedCoordinate t a (eraseCoordinate t y) =
      Function.update y t a := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m =>
      exact insertNth_eraseCoordinate_eq_update t a y



/-- Evaluation on an erased tuple recovers the corresponding
non-distinguished edge factor. -/
theorem simplexMixedCutTest_eraseCoordinate
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (t : Fin n) (y : Fin n → G) :
    simplexMixedCutTest H K j a t (eraseCoordinate t y) =
      orderedSimplexEdgeFactor H K j (j.succAbove t)
        (Fin.insertNth j a y) := by
  rw [simplexMixedCutTest,
    insertErasedCoordinate_eraseCoordinate,
    Fin.insertNth_update]
  unfold orderedSimplexEdgeFactor
  simp only [deleteCoordinate_update_same]



/-- The full product of ordered factors is the filtered product in the
telescoping definition. -/
theorem prod_orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    (∏ i : Fin k, orderedSimplexEdgeFactor H K j i x) =
      (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
        H.edgeWeight i (deleteCoordinate x i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
        K.edgeWeight i (deleteCoordinate x i) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl















end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The reconstructed cut product is exactly the product of all
non-distinguished telescoping factors. -/
theorem solution
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (y : Fin n → G) :
    (∏ t : Fin n,
        simplexMixedCutTest H K j a t
          (eraseCoordinate t y)) =
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with i < j,
        H.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with j < i,
        K.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i) := by
  simp_rw [simplexMixedCutTest_eraseCoordinate]
  calc
    (∏ t : Fin n,
        orderedSimplexEdgeFactor H K j (j.succAbove t)
          (Fin.insertNth j a y)) =
        ∏ i : Fin (n + 1),
          orderedSimplexEdgeFactor H K j i
            (Fin.insertNth j a y) := by
      symm
      calc
        (∏ i : Fin (n + 1),
            orderedSimplexEdgeFactor H K j i
              (Fin.insertNth j a y)) =
            orderedSimplexEdgeFactor H K j j
                (Fin.insertNth j a y) *
              ∏ t : Fin n,
                orderedSimplexEdgeFactor H K j
                  (j.succAbove t) (Fin.insertNth j a y) :=
          Fin.prod_univ_succAbove _ j
        _ =
            ∏ t : Fin n,
              orderedSimplexEdgeFactor H K j
                (j.succAbove t) (Fin.insertNth j a y) := by
          rw [orderedSimplexEdgeFactor_self, one_mul]
    _ = _ :=
      prod_orderedSimplexEdgeFactor H K j
        (Fin.insertNth j a y)
