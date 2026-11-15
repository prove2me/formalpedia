-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_CutDiscrepancyLe_abs_finitePairing_convolutionMixture_le
-- name    : Wikipedia.SzemeredisTheorem.CutDiscrepancyLe.abs_finitePairing_convolutionMixture_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:23.075212+00:00
-- url     : https://prove2.me/theorems/cf02a75a-d891-43f2-bac4-0fabf2db1a66
-- title:
--   Cut discrepancy controls pairings with convolution mixtures
-- statement:
--   Let $G$ be a finite additive commutative group, $\nu:G\to\mathbb R$, and $\varepsilon\in\mathbb R$. If the arity-$r$ cut discrepancy between $\nu$ and the constant function $1$ is at most $\varepsilon$, then every arity-$r$ convolution mixture $m$ satisfies $|\langle\nu-1,m\rangle|\le\varepsilon$, where the pairing is the normalized finite pairing.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionClosure.lean#L400-L426

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Multiplicative closure of generalized convolutions

The dense-model proof tests against generalized convolutions.  Products of
these tests remain convex averages of generalized convolutions: two points
in the same coordinate-sum fiber differ by a tuple of sum zero, and fixing
that difference turns the two cut products into one cut product.

This file proves the exact finite identity, packages finite convex mixtures,
and transfers a single cut-discrepancy estimate to every monomial required
by polynomial dense-model duality.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
universe u
/-! ## Finite convex mixtures -/
/-! ## Consequences for dense-model moments -/

theorem Wikipedia.SzemeredisTheorem.CutDiscrepancyLe.abs_finitePairing_convolutionMixture_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {ν : G → ℝ} {ε : ℝ}
    (hcut : CutDiscrepancyLe r ν (fun _ => 1) ε)
    (m : ConvolutionMixture G r) :
    |finitePairing (ν - fun _ => 1) m.eval| ≤ ε := by sorry
