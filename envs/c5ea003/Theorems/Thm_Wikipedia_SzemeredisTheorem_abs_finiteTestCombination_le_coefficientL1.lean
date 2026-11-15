-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finiteTestCombination_le_coefficientL1
-- name    : Wikipedia.SzemeredisTheorem.abs_finiteTestCombination_le_coefficientL1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:36.468888+00:00
-- url     : https://prove2.me/theorems/4f55b6e4-a6b3-4b57-a1a2-86c96a84b096
-- title:
--   A bounded test combination is controlled by its coefficient norm
-- statement:
--   For a finite test index type $\tau$, any family of tests taking values in $[0,1]$, coefficients $c_a\in\mathbb R$, and point $x$, the finite test combination satisfies $|\sum_a c_aq_a(x)|\le\sum_a|c_a|$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L237-L261

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Polynomial approximation in the finite dense-model argument

This file formalizes the polynomial part of the dense-model theorem.  A
normalized linear combination of `[0,1]`-valued tests takes values in
`[-1,1]`.  Weierstrass therefore approximates its positive part by a fixed
real polynomial.  Expanding that polynomial reduces correlation with the
majorant to correlations with finite products of the original tests.

The resulting estimates are quantitative and finite.  In particular, the
degree and coefficient loss of the approximating polynomial remain visible;
no asymptotic assertion about a particular pseudorandom majorant is hidden here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite products and polynomial expansions -/
/-! ## Bounded combinations and approximation of positive part -/

theorem Wikipedia.SzemeredisTheorem.abs_finiteTestCombination_le_coefficientL1
    {Ω τ : Type*} [Fintype τ]
    {q : τ → Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    (c : τ → ℝ) (x : Ω) :
    |finiteTestCombination q c x| ≤ coefficientL1 c := by sorry
