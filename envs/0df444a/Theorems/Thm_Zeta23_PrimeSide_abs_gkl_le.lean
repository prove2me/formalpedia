-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_gkl_le
-- name    : Zeta23.PrimeSide.abs_gkl_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:12:45.8925+00:00
-- url     : https://prove2.me/theorems/473d7ba2-5ddd-4506-87fa-f32c596040c8
-- title:
--   Quadratic-decay domination of the matrix-entry integrand: $|g_{kl}(\tau)| \le C_{kl}\,(1+\tau^2)^{-1}$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. For a density $\nu : \mathbb{R} \to \mathbb{R}$ and indices $k, l \in \mathbb{Z}$, the one-variable integrand of the prime-side matrix entry $G_{kl} = \int_{\mathbb{R}} g_{kl}$ is
--   $$g_{kl}(\tau) \;=\; \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau - \tau_l)\, \nu(\tau).$$
--   Assume the taper facts `LocalHypsCoreW`, the density bound `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$ for all $\tau$, [eq:Bdef]), $T \ge 1$ and $B \ge 0$. Then for every $\tau$,
--   $$|g_{kl}(\tau)| \;\le\; 4\Bigl(L + \frac{c_\varrho}{w}\Bigr)^2 (1 + \tau_k^2)(1 + \tau_l^2)(B + 1) \cdot \frac{1}{1 + \tau^2},$$
--   where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms]. The constant is crude but explicit; the point is the integrable $(1 + \tau^2)^{-1}$ decay, obtained from the shifted taper bound `abs_phiHat_shift_le` and the linear growth of $\log^+$.
--
--   This domination justifies the absolute-convergence interchanges in `eq_trG2int` ($\sum_{k,l} G_{kl}^2 = \iint K^2 \nu \nu'$) and is used directly in `lem_ends_nu_W`, the ends lemma [lem:ends] of the prime side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L217-L245

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
variable {B : ℝ}

theorem Zeta23.PrimeSide.abs_gkl_le (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 1 ≤ p.T) (hB : 0 ≤ B)
    (k l : ℤ) (τ : ℝ) :
    |gkl p F ν k l τ| ≤ (4 * (p.L + cϱ / p.w) ^ 2 * (1 + p.tau k ^ 2) * (1 + p.tau l ^ 2)
      * (B + 1)) * (1 + τ ^ 2)⁻¹ := by sorry
