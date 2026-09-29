-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_phiHat_shift_le
-- name    : Zeta23.PrimeSide.abs_phiHat_shift_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:12:32.268194+00:00
-- url     : https://prove2.me/theorems/e18721f2-6928-4860-b8c2-f5ee84579408
-- title:
--   Shifted taper decay: $|\hat\varphi(\tau - a)| \le 2(L + c_\varrho/w)\,(1 + a^2)/(1 + \tau^2)$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The theorem converts the $\psi$-majorant bounds on $\hat\varphi$ from [eq:psidef] ($|\hat\varphi(r)| \le L$ and $|\hat\varphi(r)|\, r^2 \le c_\varrho / w$) into a quadratic-decay bound centered at an arbitrary shift: for all $\tau, a \in \mathbb{R}$,
--   $$|\hat\varphi(\tau - a)| \;\le\; \frac{2\,\bigl(L + c_\varrho/w\bigr)\,(1 + a^2)}{1 + \tau^2},$$
--   where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms]. The elementary point is that $1 + \tau^2 \le (1 + a^2)(1 + (\tau - a)^2) \cdot 2$, so decay in $\tau - a$ transfers to decay in $\tau$ at the cost of a factor polynomial in $a$.
--
--   It is consumed by `abs_gkl_le`, the integrable domination of the matrix-entry integrand $g_{kl}(\tau) = \hat\varphi(\tau - \tau_k)\hat\varphi(\tau - \tau_l)\nu(\tau)$, in the ends analysis [lem:ends] of module `Zeta23.PrimeSideA.EndsCore`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L174-L187

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

theorem Zeta23.PrimeSide.abs_phiHat_shift_le (hF : LocalHypsCoreW cϱ p F) (τ a : ℝ) :
    |F.phiHat (τ - a)| ≤ 2 * (p.L + cϱ / p.w) * (1 + a ^ 2) / (1 + τ ^ 2) := by sorry
