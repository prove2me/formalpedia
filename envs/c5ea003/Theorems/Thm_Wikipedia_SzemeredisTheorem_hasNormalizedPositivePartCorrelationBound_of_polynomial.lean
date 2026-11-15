-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_hasNormalizedPositivePartCorrelationBound_of_polynomial
-- name    : Wikipedia.SzemeredisTheorem.hasNormalizedPositivePartCorrelationBound_of_polynomial
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:56.073086+00:00
-- url     : https://prove2.me/theorems/6d7a8ec3-a16a-43d1-8ced-9242cc2b4332
-- title:
--   Polynomial and monomial bounds give normalized positive-part control
-- statement:
--   Let $\Omega,\tau$ be finite and let the real tests $q_t$ take values in $[0,1]$. Suppose $\delta\ge0$, a real polynomial $p$ approximates the positive-part function uniformly on $[-1,1]$ with error $\delta$, the centered absolute mean of $\nu$ is at most $M$, and the monomial correlations through the natural degree of $p$ are absolutely bounded by $\eta$. Then every coefficient vector of $\ell^1$ norm $1$ has one-sided positive-part pairing with $\nu-1$ at most $\|p\|_{\mathrm{coeff},1}\eta+\delta M$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L362-L431

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
/-! ## Quantitative positive-part correlation -/

theorem Wikipedia.SzemeredisTheorem.hasNormalizedPositivePartCorrelationBound_of_polynomial
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    (hq : IsUnitBoundedTestFamily q)
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    HasNormalizedPositivePartCorrelationBound q ν
      (polynomialCoefficientL1 p * η + δ * M) := by sorry
