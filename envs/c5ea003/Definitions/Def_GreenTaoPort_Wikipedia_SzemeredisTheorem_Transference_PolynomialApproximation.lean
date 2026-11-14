-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:34.913114+00:00
-- url     : https://prove2.me/theorems/b0385bd2-5089-4651-917c-e0d0756488e9
-- title:
--   Test monomials and positive-part approximation data
-- statement:
--   A test monomial multiplies a finite sequence of real tests, with the empty sequence giving the constant function one. The polynomial coefficient norm is the sum of the absolute values of all coefficients.
--
--   The monomial-correlation predicate bounds the absolute normalized pairing of $\nu-1$ with every product of at most $d$ tests. A unit-bounded family has every test in $[0,1]$. The approximation predicate requires a real polynomial $p$ to satisfy $|p(x)-\max(x,0)|\le\delta$ for every $x\in[-1,1]$. The centered absolute mean is $\mathbb E|\nu-1|$. These definitions state the exact numerical inputs to the finite dense-model argument.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L24-L336

import Mathlib.Topology.ContinuousMap.Weierstrass
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators Polynomial

/-! ## Finite products and polynomial expansions -/

/-- Product of a finite sequence of tests.  The degree-zero monomial is the
constant-one function. -/
def testMonomial
    {Ω τ : Type*} (q : τ → Ω → ℝ)
    {n : ℕ} (s : Fin n → τ) : Ω → ℝ :=
  fun x => ∏ i, q (s i) x



/-- Sum of the absolute values of the coefficients of a polynomial. -/
noncomputable def polynomialCoefficientL1 (p : ℝ[X]) : ℝ :=
  ∑ n ∈ p.support, |p.coeff n|

















/-- Uniform correlation estimate for all products of at most `d` tests. -/
def HasMonomialCorrelationBound
    {Ω τ : Type*} [Fintype Ω]
    (q : τ → Ω → ℝ) (ν : Ω → ℝ)
    (d : ℕ) (η : ℝ) : Prop :=
  ∀ (n : ℕ), n ≤ d → ∀ s : Fin n → τ,
    |finitePairing (ν - fun _ => 1) (testMonomial q s)| ≤ η



/-! ## Bounded combinations and approximation of positive part -/

/-- Every member of a finite test family is pointwise in `[0,1]`. -/
def IsUnitBoundedTestFamily
    {Ω τ : Type*} (q : τ → Ω → ℝ) : Prop :=
  ∀ t, IsUnitBounded (q t)





/-- A polynomial uniformly approximates positive part on the unit interval
to the displayed error. -/
def ApproximatesPositivePartOnUnitInterval
    (p : ℝ[X]) (δ : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1,
    |p.eval x - max x 0| ≤ δ





/-! ## Quantitative positive-part correlation -/



/-- The absolute mean of the centered majorant. -/
noncomputable def centeredAbsoluteMean
    {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) : ℝ :=
  mean fun x => |ν x - 1|









end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.polynomialCoefficientL1.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


