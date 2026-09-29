-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_calE1_le_maj
-- name    : Zeta23.PrimeSide.abs_calE1_le_maj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:12:16.84125+00:00
-- url     : https://prove2.me/theorems/f7d80614-2fa2-4901-ac1e-f86b2b16d70e
-- title:
--   Integral majorization of the diagonal-block error: $|\mathcal{E}_1| \le \iint_{I\times I} \mathrm{majK1}$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). For a continuous density $\nu : \mathbb{R} \to \mathbb{R}$, the first error term of Section 5.3 is
--   $$\mathcal{E}_1 \;=\; \iint_{I \times I} \bigl(K(\tau,\tau')^2 - K_\infty(\tau,\tau')^2\bigr)\, \nu(\tau)\, \nu(\tau')\, d\tau\, d\tau',$$
--   and $\mathrm{majK1}$ is the majorant kernel $L^2\bigl(\rho(\tau)g(\tau')/g(\tau) + g(\tau)\rho(\tau')/g(\tau')\bigr)|\nu(\tau)||\nu(\tau')|$ built from the Poisson tail $\rho$ and the boundary-distance weight $g(\tau) = (1 + \min(\tau - T, 2T - \tau))^{-2}$. Assuming $\nu$ continuous, the taper facts `LocalHypsCoreW`, and $T > 0$, the theorem asserts
--   $$|\mathcal{E}_1| \;\le\; \iint_{I \times I} \mathrm{majK1}(\tau, \tau')\, d\tau\, d\tau'.$$
--   It integrates the pointwise bound `abs_E1integrand_le_majK1` over the square, the integrability bookkeeping being part of the statement's content.
--
--   Combined with `calE1_maj_bound` (which evaluates the right-hand side as $O(L^3 B^2 l)$), it disposes of $\mathcal{E}_1$ in `lem_ends_nu_W`, the $\nu$-generic ends lemma [lem:ends] equating $\operatorname{tr} \tilde G^2$ with the seam form $\mathcal{M}$ up to admissible errors.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L845-L885

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.abs_calE1_le_maj (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (_hT : 0 < p.T) :
    |calE1 p F ν| ≤ ∫ q in sqI p, majK1 p F ν q := by sorry
