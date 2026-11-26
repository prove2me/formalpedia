-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_optimizer_hessian_sub_projection_posSemidef
-- name    : ReweightedNPMLE.finite_optimizer_hessian_sub_projection_posSemidef
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:35.793936+00:00
-- url     : https://prove2.me/theorems/3ca85edd-c48f-5422-8c57-1dd4c240da45
-- title:
--   Loewner domination of the active-support tangent projection
-- statement:
--   Let $n\ge1$, let $A_1,\ldots,A_k\in(0,\infty)^n$, and let $p_j>0$ with $\sum_jp_j=1$ and $\sum_jp_jA_j=v\in(0,\infty)^n$. Let $w\in(0,\infty)^n$. On a convex set $C\supset\{A_j\}$, suppose $\widehat v(q)$ maximizes $L_q(z)=\sum_iq_i\log z_i$ for every $q\in\mathbb R^n$, with $\widehat v(w)=v$. Put $\Psi(q)=L_q(\widehat v(q))$ and $z(q)=\log\widehat v(q)$ coordinatewise. Because $C$ is not assumed to lie in the positive orthant, these functions use the total real logarithm: the usual $\log|t|$ for $t\ne0$, and $\log0=0$. Assume $D\Psi(q)[h]=\langle z(q),h\rangle$ throughout a neighborhood of $w$, and $Dz(w)=J$. Define $u(c)_i=\sum_jc_jA_{ji}/v_i$, $D_w=\operatorname{diag}(\sqrt w)$, and $S=\{D_wu(c):\sum_jc_j=0\}$. Let $V$ have as columns the canonical orthonormal basis of $S$, and set $R=D_w[J]D_w$. Then $$R-VV^\mathsf T\succeq0.$$ Thus the square-root-weight-conjugated fitted-log derivative dominates the orthogonal projection onto the active tangent space. Extremality of the coefficient vector is not needed for this statement.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L410-L449

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

theorem ReweightedNPMLE.finite_optimizer_hessian_sub_projection_posSemidef
    {k n : ℕ} [Nonempty (Fin n)]
    (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin k → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hpfull : ∀ j, 0 < p j)
    (hvpos : ∀ i, 0 < v i) (hApos : ∀ j i, 0 < A j i)
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C) (hA : Set.range A ⊆ C)
    (hmax : ∀ q, IsMaxOn C (weightedLogLikelihood q) (vhat q))
    (hvw : vhat w = v)
    (hpsi : ∀ᶠ q in nhds w, HasFDerivAt (fittedOptimalValue vhat)
      (fittedLogLinearFunctional (fun i ↦ Real.log (vhat q i))) q)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun q i ↦ Real.log (vhat q i)) J w) :
    let S := weightedRelativeTangentSpace A v w
    let V := submoduleOrthonormalMatrix S
    let R := Matrix.diagonal (fun i ↦ Real.sqrt (w i)) *
      fittedLogDerivativeMatrix J *
      Matrix.diagonal (fun i ↦ Real.sqrt (w i))
    (R - V * Vᴴ).PosSemidef := by sorry
