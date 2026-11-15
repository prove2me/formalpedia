-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_polynomial_eval_finiteTestCombination
-- name    : Wikipedia.SzemeredisTheorem.finitePairing_polynomial_eval_finiteTestCombination
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:49.426188+00:00
-- url     : https://prove2.me/theorems/54fe169d-ce10-4834-8b56-d226bbd21d76
-- title:
--   Expanding a polynomial test combination inside a finite pairing
-- statement:
--   For finite types $\Omega,\tau$, real $f$, polynomial $p$, tests $q_t$, and coefficients $c_t$, the pairing of $f$ with $p$ evaluated on their finite test combination equals the sum over $n$ in the support of $p$ and maps $s:\mathrm{Fin}(n)\to\tau$ of $(p_n\prod_i c_{s(i)})\langle f,\operatorname{testMonomial}(q,s)\rangle$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/PolynomialApproximation.lean#L117-L150

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

theorem Wikipedia.SzemeredisTheorem.finitePairing_polynomial_eval_finiteTestCombination
    {Ω τ : Type*} [Fintype Ω] [Fintype τ]
    (f : Ω → ℝ) (p : ℝ[X])
    (q : τ → Ω → ℝ) (c : τ → ℝ) :
    finitePairing f
        (fun x => p.eval (finiteTestCombination q c x)) =
      ∑ n ∈ p.support,
        ∑ s : Fin n → τ,
          (p.coeff n * ∏ i, c (s i)) *
            finitePairing f (testMonomial q s) := by sorry
