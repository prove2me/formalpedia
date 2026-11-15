-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finitePairing_polynomial_eval_le
-- name    : Wikipedia.SzemeredisTheorem.abs_finitePairing_polynomial_eval_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:39.209955+00:00
-- url     : https://prove2.me/theorems/0ce63d69-5570-436a-a0af-cf073d9cf3f0
-- title:
--   A polynomial pairing bound from monomial correlations
-- statement:
--   Let $\Omega,\tau$ be finite types, $q_a$ real tests, $\nu:\Omega\to\mathbb R$, and $p\in\mathbb R[X]$. If the coefficient vector $c$ has $\ell^1$ norm $1$ and the tests satisfy the monomial-correlation bound for $\nu$ through the natural degree of $p$ with error $\eta$, then the pairing of $\nu-1$ with $p$ evaluated on the finite test combination has absolute value at most the coefficient $\ell^1$ norm of $p$ times $\eta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L174-L228

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

theorem Wikipedia.SzemeredisTheorem.abs_finitePairing_polynomial_eval_le
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    {q : τ → Ω → ℝ} {ν : Ω → ℝ}
    {η : ℝ} (p : ℝ[X]) (c : τ → ℝ)
    (hc : coefficientL1 c = 1)
    (hmono :
      HasMonomialCorrelationBound q ν p.natDegree η) :
    |finitePairing (ν - fun _ => 1)
        (fun x => p.eval (finiteTestCombination q c x))| ≤
      polynomialCoefficientL1 p * η := by sorry
