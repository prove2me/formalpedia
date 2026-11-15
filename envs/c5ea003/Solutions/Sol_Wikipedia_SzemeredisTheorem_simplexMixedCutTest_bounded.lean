-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.simplexMixedCutTest_bounded
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:30:19.063203+00:00
-- url     : https://prove2.me/submissions/b5262916-0d42-40ad-ba2d-afb6953cd9e4

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
/-- Unit-interval edge bounds make the reconstructed cut family bounded. -/
theorem solution
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) (a : G) :
    IsBoundedCutTest (simplexMixedCutTest H K j a) := by
  constructor
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simp [htj, hjt, (hH _ _).1]
    · by_cases hjt : j < j.succAbove t
      · simp [htj, hjt, (hK _ _).1]
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simpa [htj, hjt] using
        (hH (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j a (insertErasedCoordinate t a z))
            (j.succAbove t))).2
    · by_cases hjt : j < j.succAbove t
      · simpa [htj, hjt] using
          (hK (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j a (insertErasedCoordinate t a z))
              (j.succAbove t))).2
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim
