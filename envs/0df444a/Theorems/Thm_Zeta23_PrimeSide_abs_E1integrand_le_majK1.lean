-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_E1integrand_le_majK1
-- name    : Zeta23.PrimeSide.abs_E1integrand_le_majK1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:11:10.918792+00:00
-- url     : https://prove2.me/theorems/fbdbc09e-46e2-4f61-a4ae-30cf8fc36a4b
-- title:
--   Pointwise majorant for the $\mathcal{E}_1$ integrand: $|K^2 - K_\infty^2|\,|\nu\nu'| \le \mathrm{majK1}$ on $I \times I$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). Set $\rho(\tau) = a L^2 - \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)^2$ (the tail of the Poisson diagonal) and let $g(\tau) = \bigl(1 + \min(\tau - T,\, 2T - \tau)\bigr)^{-2}$ be the boundary-distance weight on $I$. The majorant kernel is
--   $$\mathrm{majK1}(\tau,\tau') = L^2\Bigl(\tfrac{\rho(\tau)}{g(\tau)}\,g(\tau') + g(\tau)\,\tfrac{\rho(\tau')}{g(\tau')}\Bigr)\,|\nu(\tau)|\,|\nu(\tau')|,$$
--   where $\nu : \mathbb{R} \to \mathbb{R}$ is an arbitrary density. The theorem asserts the pointwise bound: for every $q = (\tau, \tau') \in I \times I$,
--   $$\bigl|K(\tau,\tau')^2\,\nu(\tau)\,\nu(\tau') - K_\infty(\tau,\tau')^2\,\nu(\tau)\,\nu(\tau')\bigr| \;\le\; \mathrm{majK1}(\tau,\tau').$$
--   The proof factors $K^2 - K_\infty^2 = (K - K_\infty)(K + K_\infty)$ and applies the weighted AM–GM tail bound `abs_Kinf_sub_Kfun_le` with weight $s = g(\tau')/g(\tau)$, together with $|K|, |K_\infty| \le L^2$; note the resulting majorant kernel is independent of $\nu$ apart from the factor $|\nu(\tau)||\nu(\tau')|$.
--
--   In the project this is the pointwise input to `abs_calE1_le_maj`, which integrates it over $I \times I$ to bound the error term $\mathcal{E}_1$ in the ends analysis (module `Zeta23.PrimeSideA.EndsE1`, part of the proof of [lem:ends]).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L198-L229

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

theorem Zeta23.PrimeSide.abs_E1integrand_le_majK1 (hF : LocalHypsCoreW cϱ p F) {q : ℝ × ℝ} (hq : q ∈ sqI p) :
    |trG2integrand p F ν q - KinfIntegrand p F ν q| ≤ majK1 p F ν q := by sorry
