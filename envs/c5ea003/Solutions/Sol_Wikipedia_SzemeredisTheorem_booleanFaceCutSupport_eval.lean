-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.booleanFaceCutSupport_eval
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:23:57.876954+00:00
-- url     : https://prove2.me/submissions/d037c0e6-7c52-420b-9b90-7ce471d9a63c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Partition.Finpartition
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The indicator of a Boolean cut support is exactly the corresponding
product of Boolean lower-face tests. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (b : BooleanCutAssignment G r) (x : Fin r → G) :
    (booleanFaceCutSupport b).eval x =
      cutTestProduct (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  by_cases h : ∀ i, b ⟨i, eraseCoordinate i x⟩ = true
  · have hx : x ∈ booleanFaceCutSupport b := by
      simp [booleanFaceCutSupport, h]
    rw [BooleanCutTest.eval_of_mem _ hx]
    unfold cutTestProduct
    symm
    apply Finset.prod_eq_one
    intro i _
    simp [cutTestFamilyOfBooleanAssignment, booleanValue, h i]
  · have hx : x ∉ booleanFaceCutSupport b := by
      simpa [booleanFaceCutSupport] using h
    rw [BooleanCutTest.eval_of_not_mem _ hx]
    obtain ⟨i, hi⟩ := not_forall.mp h
    cases hb : b ⟨i, eraseCoordinate i x⟩ with
    | false =>
        unfold cutTestProduct
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [cutTestFamilyOfBooleanAssignment,
          booleanValue, hb]
    | true =>
        exact (hi hb).elim
