-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutCorrelation_eq_sum_boolean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:12.616203+00:00
-- url     : https://prove2.me/submissions/241c47eb-a40c-4f87-aad5-af12941a9b26

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
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
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite Bernoulli mixtures -/
/-! ## Boolean cut coordinates -/

open Wikipedia.SzemeredisTheorem in
/-- Exact convex-mixture formula for a cut correlation. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold cutCorrelation
  calc
    mean (fun x : Fin r → G =>
        (f (∑ i, x i) - g (∑ i, x i)) *
          ∏ i, u i (eraseCoordinate i x)) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              ((f (∑ i, x i) - g (∑ i, x i)) *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      change
        (f (∑ i, x i) - g (∑ i, x i)) *
            cutTestProduct u x =
          _
      rw [cutTestProduct_eq_sum_boolean u x]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ = ∑ b : BooleanCutAssignment G r,
        mean (fun x : Fin r → G =>
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ = ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          mean (fun x : Fin r → G =>
            (f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl
