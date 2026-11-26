-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_extreme_optimizer_hessian_determinant_lower
-- name    : ReweightedNPMLE.finite_extreme_optimizer_hessian_determinant_lower
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:01.296087+00:00
-- url     : https://prove2.me/theorems/bd7debaa-282b-455d-b486-0a7eddd505d3
-- title:
--   Determinant gain from a k-atom extreme optimizer
-- statement:
--   Let $n\ge1$, let $A_1,\ldots,A_k\in(0,\infty)^n$, and let $p_j>0$ with $\sum_jp_j=1$ and $\sum_jp_jA_j=v\in(0,\infty)^n$. Let $w\in(0,\infty)^n$. On a convex set $C\supset\{A_j\}$, suppose $\widehat v(q)$ maximizes $L_q(z)=\sum_iq_i\log z_i$ for every $q\in\mathbb R^n$, with $\widehat v(w)=v$. Put $\Psi(q)=L_q(\widehat v(q))$ and $z(q)=\log\widehat v(q)$ coordinatewise. Because $C$ is not assumed to lie in the positive orthant, these functions use the total real logarithm: the usual $\log|t|$ for $t\ne0$, and $\log0=0$. Assume $D\Psi(q)[h]=\langle z(q),h\rangle$ throughout a neighborhood of $w$, and $Dz(w)=J$. Define $u(c)_i=\sum_jc_jA_{ji}/v_i$, $D_w=\operatorname{diag}(\sqrt w)$, and $S=\{D_wu(c):\sum_jc_j=0\}$. Let $V$ have as columns the canonical orthonormal basis of $S$, and set $R=D_w[J]D_w$. Assume $k\ge1$ and that $p$ is extreme in its finite moment fiber. For any $a\in\mathbb R^n$ with $0<a_i\le9/8$, $$\det(\operatorname{diag}(a)+R)\ge\left(\prod_i a_i\right)(17/9)^{k-1}.$$ This quantitative gain connects optimizer support size with the change-of-variables Jacobian.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L451-L493

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.finite_extreme_optimizer_hessian_determinant_lower
    {k n : ℕ} [Nonempty (Fin k)] [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (hextreme : p ∈ (finiteMixtureFiber A v).extremePoints ℝ)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w)
    (a : Fin n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ (k - 1) ≤
      (Matrix.diagonal a + Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
        fittedLogDerivativeMatrix J *
        Matrix.diagonal (fun i ↦ Real.sqrt (w i))).det := by sorry
