-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.FaceRegularityState.faceCutCorrelation_eq_sum_boolean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:12.724488+00:00
-- url     : https://prove2.me/submissions/a4a19f06-d705-430e-8469-c5f0a3ed729f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_bernoulliAssignmentWeight_mul_selected

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
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite Bernoulli mixtures -/











/-- Bernoulli moment pulled back along an embedding. -/
theorem sum_bernoulliAssignmentWeight_mul_embedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i : ι, booleanValue b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (sum_bernoulliAssignmentWeight_mul_selected p
      (Finset.univ.map e))

/-! ## Boolean cut coordinates -/













@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

/-- Exact Bernoulli mixture identity for one product of cut tests. -/
theorem cutTestProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) :
    cutTestProduct u x =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  symm
  simpa [cutTestProduct, cutTestCoordinateValue,
    cutTestFamilyOfBooleanAssignment,
    usedCutTestCoordinateEmbedding_apply] using
    (sum_bernoulliAssignmentWeight_mul_embedding
      (cutTestCoordinateValue u)
      (usedCutTestCoordinateEmbedding x))





/-! ## The finite dense-model test family -/















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
open Wikipedia.SzemeredisTheorem.FaceRegularityState

open Wikipedia.SzemeredisTheorem.FaceRegularityState in
/-- Exact Bernoulli-mixture formula for one face-cut correlation. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (S : FaceRegularityState (Fin r → G))
    (f : (Fin r → G) → ℝ) (u : CutTestFamily G r) :
    S.faceCutCorrelation f u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          S.faceCutCorrelation f
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold faceCutCorrelation
  calc
    mean (fun x : Fin r → G =>
        S.residual f x * cutTestProduct u x) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      rw [cutTestProduct_eq_sum_boolean u x,
        Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ =
        ∑ b : BooleanCutAssignment G r,
          mean (fun x : Fin r → G =>
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              (S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ =
        ∑ b : BooleanCutAssignment G r,
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            mean (fun x : Fin r → G =>
              S.residual f x *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl
