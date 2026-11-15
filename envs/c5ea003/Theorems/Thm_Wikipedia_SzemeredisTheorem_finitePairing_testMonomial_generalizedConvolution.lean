-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_finitePairing_testMonomial_generalizedConvolution
-- name    : Wikipedia.SzemeredisTheorem.finitePairing_testMonomial_generalizedConvolution
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:51.389863+00:00
-- url     : https://prove2.me/theorems/18c7e158-978a-49b8-aebd-80a0338e7af4
-- title:
--   A convolution monomial pairing equals its expanded fiber moment
-- statement:
--   Let $G$ be a finite additive commutative group, let $r\in\mathbb N$ and $\nu:G\to\mathbb R$, and let $u_t$ be arity-$(r+1)$ cut tests indexed by any type $\tau$. For a finite selection $s:\mathrm{Fin}(n)\to\tau$, pairing $\nu-1$ with the corresponding monomial of generalized convolutions equals the convolution monomial moment of the selected tests.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionMoments.lean#L44-L66

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
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
# Moments of generalized convolutions

Products of generalized convolutions are averages over independent copies of
the corresponding sum fibers.  This file records that disintegration
exactly and packages the remaining analytic estimate as a concrete moment
condition.  It is the interface at which iterated Cauchy--Schwarz and the
linear-forms estimate enter the dense-model proof.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial

theorem Wikipedia.SzemeredisTheorem.finitePairing_testMonomial_generalizedConvolution
    {G τ : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (ν : G → ℝ)
    (u : τ → CutTestFamily G (r + 1))
    {n : ℕ} (s : Fin n → τ) :
    finitePairing (ν - fun _ => 1)
        (testMonomial
          (fun t => generalizedConvolution (r + 1) (u t)) s) =
      convolutionMonomialMoment r ν (fun a => u (s a)) := by sorry
