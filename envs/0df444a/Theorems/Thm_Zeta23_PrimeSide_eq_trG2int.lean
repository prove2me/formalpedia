-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_eq_trG2int
-- name    : Zeta23.PrimeSide.eq_trG2int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:20:18.685162+00:00
-- url     : https://prove2.me/theorems/14382526-42a2-4204-80e5-0ed21bdd438a
-- title:
--   The squared trace as a double integral [eq:trG2int]: $\sum_{k,l<d} G_{kl}^2 = \iint_{\mathbb{R}^2} K(\tau,\tau')^2\, \nu(\tau)\nu(\tau')\, d\tau\, d\tau'$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. For a density $\nu : \mathbb{R} \to \mathbb{R}$, the prime-side matrix entries are $G_{kl} = \int_{\mathbb{R}} \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau - \tau_l)\, \nu(\tau)\, d\tau$ ([eq:Gdef], second expression, here for an abstract $\nu$), and $K(\tau, \tau') = \sum_{0 \le k < d} \hat\varphi(\tau - \tau_k)\hat\varphi(\tau' - \tau_k)$ [eq:Kdef]. Assume $\nu$ continuous, the taper facts `LocalHypsCoreW`, the density bound `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$) with $B \ge 0$, and $T \ge 2\pi$. The theorem is the identity [eq:trG2int] of Section 5.3:
--   $$\sum_{0 \le k < d}\, \sum_{0 \le l < d} G_{kl}^2 \;=\; \iint_{\mathbb{R}^2} K(\tau, \tau')^2\, \nu(\tau)\, \nu(\tau')\, d\tau\, d\tau',$$
--   obtained by expanding each $G_{kl}^2$ as a double integral and interchanging sum and integral, the interchange being justified by absolute convergence (via the domination `abs_gkl_le`).
--
--   This converts $\operatorname{tr}\tilde{G}^2 = L^{-2}\sum_{k,l} G_{kl}^2$ into kernel form, the starting point of the ends analysis; it is consumed by `lem_ends_nu_W`, the $\nu$-generic ends lemma [lem:ends] (module `Zeta23.PrimeSideA.EndsCore`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L281-L301, docstring tag [eq:trG2int]

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

theorem Zeta23.PrimeSide.eq_trG2int (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hB : 0 ≤ B) (hT : 2 * π ≤ p.T) :
    ∑ k : Fin p.d, ∑ l : Fin p.d, GentryNu ν p F k l ^ 2 = ∫ q, trG2integrand p F ν q := by sorry
