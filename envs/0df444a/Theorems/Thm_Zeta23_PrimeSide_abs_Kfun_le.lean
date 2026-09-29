-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Kfun_le
-- name    : Zeta23.PrimeSide.abs_Kfun_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:10:23.532714+00:00
-- url     : https://prove2.me/theorems/1d00837e-f0c0-4139-be4d-dd8f5cbf800f
-- title:
--   Uniform kernel bound $|K(\tau,\tau')| \le L^2$ [eq:Kbounds]
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). The theorem is the first part of [eq:Kbounds]: for all $\tau, \tau' \in \mathbb{R}$,
--   $$|K(\tau,\tau')| \;\le\; L^2.$$
--   The proof is Cauchy–Schwarz over the grid sum combined with the Poisson diagonal identity $\sum_{k \in \mathbb{Z}} \hat\varphi(\tau - \tau_k)^2 = L\,\Phi(0) = a L^2$ and $a \le 1$ (the paper's sharper intermediate bound is $|K| \le a L^2$).
--
--   This uniform bound feeds the pointwise majorants of the ends analysis: it is used in `abs_E1integrand_le_majK1` (the $\mathcal{E}_1$ integrand bound) and `abs_trG2integrand_le` (the $\mathcal{E}_2$ majorant), both part of the proof of [lem:ends] on the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L582-L603, docstring tag [eq:Kbounds]

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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)
variable {p F ν}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.abs_Kfun_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) : |Kfun p F τ τ'| ≤ p.L ^ 2 := by sorry
