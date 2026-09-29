-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_calE1_maj_bound
-- name    : Zeta23.PrimeSide.calE1_maj_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:14:40.158202+00:00
-- url     : https://prove2.me/theorems/ded1876f-2d90-4f34-b4b0-2bb69049224b
-- title:
--   The $\mathcal{E}_1$ majorant integral is $O(L^3 B^2 l)$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The majorant kernel is $\mathrm{majK1}(\tau,\tau') = L^2\bigl(\rho(\tau)g(\tau')/g(\tau) + g(\tau)\rho(\tau')/g(\tau')\bigr)\,|\nu(\tau)||\nu(\tau')|$, built from the Poisson tail $\rho(\tau) = aL^2 - \sum_{0 \le k < d}\hat\varphi(\tau-\tau_k)^2$ and the boundary-distance weight $g(\tau) = (1 + \min(\tau - T, 2T - \tau))^{-2}$. Fix the profile constant $c_\varrho$ and the bandwidth ratio $\lambda$. The theorem asserts the existence of constants $C$ and $T_0$ such that for every setting $p$ with $p.\mathrm{lam} = \lambda$ and $T \ge T_0$, every taper datum $F$ satisfying `LocalHypsCoreW`, and every continuous density $\nu$ with the bound `NuBound` ($|\nu(\tau)| \le B + \log^+(|\tau|/4T)$), provided also $L \le 2l$,
--   $$\iint_{I \times I} \mathrm{majK1}(\tau, \tau')\, d\tau\, d\tau' \;\le\; C\, L^3\, B^2\, l.$$
--   The gain over the trivial $L^4 B^2 T$ comes from $\int_I g \le 2$ and the smallness of the Poisson tail $\rho$ away from the boundary of $I$.
--
--   Together with `abs_calE1_le_maj` ($|\mathcal{E}_1| \le \iint \mathrm{majK1}$), this bounds the diagonal-block error $\mathcal{E}_1$ in `lem_ends_nu_W`, the ends lemma [lem:ends] equating $\operatorname{tr}\tilde G^2$ with the seam form $\mathcal{M}$ up to $O(L\, l \log l\, (l^2 + X))$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L617-L724

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
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.calE1_maj_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν →
      ∫ q in sqI p, majK1 p F ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l) := by sorry
