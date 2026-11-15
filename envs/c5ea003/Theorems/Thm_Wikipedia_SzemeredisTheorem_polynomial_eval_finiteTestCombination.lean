-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_polynomial_eval_finiteTestCombination
-- name    : Wikipedia.SzemeredisTheorem.polynomial_eval_finiteTestCombination
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:25:49.590875+00:00
-- url     : https://prove2.me/theorems/ed6d02a1-8f1e-4541-8b77-c5930f7831b0
-- title:
--   Expanding a polynomial of a finite test combination
-- statement:
--   Let $\tau$ be finite, let $p\in\mathbb R[X]$, let $q_a:\Omega\to\mathbb R$ be tests, and let $c_a\in\mathbb R$ be coefficients. At any $x\in\Omega$, evaluating $p$ on the finite test combination equals the sum over $n$ in the polynomial support and maps $s:\mathrm{Fin}(n)\to\tau$ of $p_n(\prod_i c_{s(i)})$ times the test monomial indexed by $s$ at $x$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L94-L115

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

theorem Wikipedia.SzemeredisTheorem.polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype τ]
    (p : ℝ[X]) (q : τ → Ω → ℝ) (c : τ → ℝ) (x : Ω) :
    p.eval (finiteTestCombination q c x) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            testMonomial q s x := by sorry
