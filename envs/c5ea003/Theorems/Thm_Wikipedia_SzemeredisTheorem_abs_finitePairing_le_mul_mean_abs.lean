-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_finitePairing_le_mul_mean_abs
-- name    : Wikipedia.SzemeredisTheorem.abs_finitePairing_le_mul_mean_abs
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:35.652208+00:00
-- url     : https://prove2.me/theorems/7a74cd42-3cd3-4d53-ab22-97c9e0d01a2e
-- title:
--   A bounded error controls a finite pairing by mean absolute size
-- statement:
--   Let $\Omega$ be finite and $f,e:\Omega\to\mathbb R$. If $|e(x)|\le\delta$ for every $x$, then the absolute normalized finite pairing satisfies $|\langle f,e\rangle|\le\delta\,\mathbb E_x|f(x)|$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L312-L331

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

theorem Wikipedia.SzemeredisTheorem.abs_finitePairing_le_mul_mean_abs
    {Ω : Type*} [Fintype Ω]
    (f e : Ω → ℝ) {δ : ℝ}
    (he : ∀ x, |e x| ≤ δ) :
    |finitePairing f e| ≤ δ * mean (fun x => |f x|) := by sorry
