-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_cutCorrelation_le_of_boolean
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:54.896799+00:00
-- url     : https://prove2.me/submissions/7848409a-92a4-40eb-93ca-5fde04136ed7

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutCorrelation_eq_sum_boolean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_bernoulliAssignmentWeight

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





theorem bernoulliAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ bernoulliAssignmentWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using hp0 i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [hp1 i]







/-! ## Boolean cut coordinates -/





















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
/-- It is enough to bound all Boolean cut correlations. -/
theorem solution
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BooleanCutAssignment G r,
        |cutCorrelation r f g
          (cutTestFamilyOfBooleanAssignment b)| ≤ ε) :
    |cutCorrelation r f g u| ≤ ε := by
  classical
  rw [cutCorrelation_eq_sum_boolean]
  calc
    |∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b)| ≤
        ∑ b : BooleanCutAssignment G r,
          |bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            cutCorrelation r f g
              (cutTestFamilyOfBooleanAssignment b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw :
          0 ≤ bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b :=
        bernoulliAssignmentWeight_nonneg
          (p := cutTestCoordinateValue u)
          (fun q => hu.nonneg q.1 q.2)
          (fun q => hu.le_one q.1 q.2) b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_bernoulliAssignmentWeight, one_mul]
