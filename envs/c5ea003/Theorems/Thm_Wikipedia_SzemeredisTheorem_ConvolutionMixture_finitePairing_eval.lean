-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_ConvolutionMixture_finitePairing_eval
-- name    : Wikipedia.SzemeredisTheorem.ConvolutionMixture.finitePairing_eval
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:23.564804+00:00
-- url     : https://prove2.me/theorems/0710265c-62aa-460b-b1d6-93e6655a2c86
-- title:
--   Pairing commutes with convolution-mixture averaging
-- statement:
--   Let $G$ be a finite additive commutative group, $m$ a convolution mixture of arity $r$, and $h:G\to\mathbb R$. The finite pairing of $h$ with the evaluation of $m$ equals the normalized mean, over the finite index type of $m$, of the pairings of $h$ with its constituent generalized convolutions.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionClosure.lean#L360-L394

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
open Wikipedia.SzemeredisTheorem.ConvolutionMixture

theorem Wikipedia.SzemeredisTheorem.ConvolutionMixture.finitePairing_eval
    {G : Type u} [Fintype G] [AddCommGroup G] {r : ℕ}
    (m : ConvolutionMixture G r) (h : G → ℝ) :
    finitePairing h m.eval =
      letI : Fintype m.ι := m.indexFintype
      mean (fun a =>
        finitePairing h
          (generalizedConvolution r (m.tests a))) := by sorry
