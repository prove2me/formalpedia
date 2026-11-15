-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_bernoulliAssignmentWeight
-- name    : Wikipedia.SzemeredisTheorem.sum_bernoulliAssignmentWeight
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:29:32.273277+00:00
-- url     : https://prove2.me/theorems/a2c9b26f-ed2e-4d53-89c1-665585e7b581
-- title:
--   Bernoulli assignment weights sum to one
-- statement:
--   For any finite index type $\kappa$ with decidable equality and arbitrary real parameter function $p:\kappa\to\mathbb R$, the Bernoulli assignment weights sum to $1$ over all Boolean assignments. The algebraic identity does not require $p$ to lie in $[0,1]$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean#L44-L64

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

theorem Wikipedia.SzemeredisTheorem.sum_bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by sorry
