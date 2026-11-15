-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_ConvolutionMixture_exists_eq_prod_generalizedConvolution
-- name    : Wikipedia.SzemeredisTheorem.ConvolutionMixture.exists_eq_prod_generalizedConvolution
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:35.634511+00:00
-- url     : https://prove2.me/theorems/4713f85a-4488-49eb-b761-6bc562ff4627
-- title:
--   Finite products of bounded convolutions are mixtures
-- statement:
--   Let $G$ be a finite additive commutative group and $r,m\in\mathbb N$. For a family $u_a$ of bounded cut tests of arity $r+1$, indexed by $a\in\mathrm{Fin}(m)$, there is a convolution mixture $q$ of that arity such that $q(z)=\prod_a\operatorname{generalizedConvolution}_{r+1}(u_a)(z)$ for every $z\in G$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/ConvolutionClosure.lean#L331-L358

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

theorem Wikipedia.SzemeredisTheorem.ConvolutionMixture.exists_eq_prod_generalizedConvolution
    {G : Type u} [Fintype G] [AddCommGroup G] (r : ℕ) :
    ∀ (m : ℕ) (u : Fin m → CutTestFamily G (r + 1)),
      (∀ a, IsBoundedCutTest (u a)) →
      ∃ q : ConvolutionMixture G (r + 1),
        q.eval =
          fun z => ∏ a,
            generalizedConvolution (r + 1) (u a) z := by sorry
