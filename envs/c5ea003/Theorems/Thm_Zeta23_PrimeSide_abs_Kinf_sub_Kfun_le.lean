-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Kinf_sub_Kfun_le
-- name    : Zeta23.PrimeSide.abs_Kinf_sub_Kfun_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:10:56.437367+00:00
-- url     : https://prove2.me/theorems/a13bb842-6dc3-4f04-8688-60e012dd9a6d
-- title:
--   Weighted AM–GM bound for the kernel tail $|K_\infty - K| \le \tfrac12\bigl(s\rho(\tau) + \rho(\tau')/s\bigr)$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). Set $\rho(\tau) = a L^2 - \sum_{0 \le k < d} \hat\varphi(\tau - \tau_k)^2$; by the Poisson diagonal this equals the tail $\sum_{k \notin [0,d)} \hat\varphi(\tau - \tau_k)^2 \ge 0$. The theorem is a pointwise bound for the out-of-window part $K_{\mathrm{out}} = K_\infty - K$: for all $\tau, \tau' \in \mathbb{R}$ and every weight $s > 0$,
--   $$\bigl|K_\infty(\tau,\tau') - K(\tau,\tau')\bigr| \;\le\; \frac{s\,\rho(\tau) + \rho(\tau')/s}{2}.$$
--   The proof writes $K_\infty - K$ as the absolutely convergent sum over $k \notin [0, d)$ of $\hat\varphi(\tau-\tau_k)\hat\varphi(\tau'-\tau_k)$ (`hasSum_Kout`) and applies the weighted AM–GM inequality $|uv| \le \tfrac12(s u^2 + v^2/s)$ termwise.
--
--   With the choice $s = g(\tau')/g(\tau)$ (a ratio of boundary-distance weights) this yields the $\mathcal{E}_1$ majorant in `abs_E1integrand_le_majK1`, part of the ends analysis [lem:ends] in module `Zeta23.PrimeSideA.EndsCore`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L669-L692

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

theorem Zeta23.PrimeSide.abs_Kinf_sub_Kfun_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) {s : ℝ} (hs : 0 < s) :
    |Kinf p F τ τ' - Kfun p F τ τ'| ≤ (s * rho p F τ + rho p F τ' / s) / 2 := by sorry
