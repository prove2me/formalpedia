-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_hasSum_Kout
-- name    : Zeta23.PrimeSide.hasSum_Kout
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:10:40.156759+00:00
-- url     : https://prove2.me/theorems/5976e64e-b923-4871-bac9-25ea9eba898f
-- title:
--   $K_\infty - K$ is the convergent tail sum over off-window grid points
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The kernels are $K(\tau,\tau') = \sum_{0 \le k < d} \hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau'-\tau_k)$ [eq:Kdef] and its full-lattice completion $K_\infty(\tau,\tau') = L\,\Phi(\tau-\tau')$ (the value of the sum over all $k \in \mathbb{Z}$, by Poisson summation [lem:poisson]). The theorem asserts that for all $\tau, \tau' \in \mathbb{R}$ the family
--   $$k \;\longmapsto\; \hat\varphi(\tau - \tau_k)\, \hat\varphi(\tau' - \tau_k), \qquad k \in \mathbb{Z} \setminus [0, d),$$
--   is summable (in the strong `HasSum` sense of Mathlib, i.e. unconditionally) with sum exactly $K_\infty(\tau, \tau') - K(\tau, \tau')$. This follows from the Poisson summation field of the taper hypotheses ([lem:poisson]: the full sum over $k \in \mathbb{Z}$ has value $L\,\Phi(\tau - \tau') = K_\infty$) by subtracting the finitely many in-window terms constituting $K$.
--
--   It realizes the out-of-window kernel $K_{\mathrm{out}} = K_\infty - K$ as a genuine sum, which is then estimated termwise by weighted AM–GM in `abs_Kinf_sub_Kfun_le`, the pointwise tail bound of the ends analysis [lem:ends] (module `Zeta23.PrimeSideA.EndsCore`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L640-L655

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

theorem Zeta23.PrimeSide.hasSum_Kout (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    HasSum (fun k : {k : ℤ // k ∉ Finset.Ico (0 : ℤ) p.d} =>
      F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
      (Kinf p F τ τ' - Kfun p F τ τ') := by sorry
