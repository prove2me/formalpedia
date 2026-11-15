-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cutDiscrepancy_model_of_monomialCorrelationBound
-- name    : Wikipedia.SzemeredisTheorem.exists_cutDiscrepancy_model_of_monomialCorrelationBound
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:46.7571+00:00
-- url     : https://prove2.me/theorems/0852fa81-a2a1-486c-8158-9e0c3526089b
-- title:
--   A monomial correlation bound gives a cut-discrepancy dense model
-- statement:
--   Let $G$ be a finite additive commutative group, $r>0$, and $0\le f\le\nu$. Let $\delta,\eta,M\ge0$, and let a real polynomial $p$ approximate the positive-part function uniformly on $[-1,1]$ with error $\delta$. Assume the centered absolute mean of $\nu$ is at most $M$ and the Boolean cut-convolution tests satisfy the monomial-correlation bound through the natural degree of $p$ with error $\eta$. Then there is $g:G\to[0,1]$ whose arity-$r$ cut discrepancy from $f$ is at most $\|p\|_{\mathrm{coeff},1}\eta+\delta M$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean#L370-L400

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
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
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite Bernoulli mixtures -/
/-! ## Boolean cut coordinates -/
/-! ## The finite dense-model test family -/

theorem Wikipedia.SzemeredisTheorem.exists_cutDiscrepancy_model_of_monomialCorrelationBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (hr : 0 < r)
    {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound
        (booleanCutConvolution (G := G) r)
        ν p.natDegree η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g
        (polynomialCoefficientL1 p * η + δ * M) := by sorry
