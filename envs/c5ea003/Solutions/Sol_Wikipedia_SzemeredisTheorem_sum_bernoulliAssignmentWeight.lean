-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_bernoulliAssignmentWeight
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:54.693928+00:00
-- url     : https://prove2.me/submissions/bcdda360-4919-4a1b-982d-d4977632bf41

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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

open Wikipedia.SzemeredisTheorem in
/-- Product Bernoulli weights sum to one. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp
