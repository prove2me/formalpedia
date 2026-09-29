-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_eq_Msplit
-- name    : Zeta23.PrimeSide.eq_Msplit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:23:22.985041+00:00
-- url     : https://prove2.me/theorems/50e43ae7-2ba4-4eda-95de-69102c9f7903
-- title:
--   Bilinear splitting of the seam form [eq:Msplit]: $\mathcal{M}$ as six terms in $\mu$, $P_X$, $\Pi_X$
-- statement:
--   Throughout, $p$ is an abstract prime-side parameter setting with height $T$, bandwidth ratio $\lambda$, and ramp width $w$; derived from these are $l = \log(T/2\pi)$, the window length $L = \lambda l$, the grid spacing $h = 2\pi/L$, the grid size $d = \lfloor LT/2\pi \rfloor$, the grid points $\tau_k = T + kh$, and the window $I = [T, 2T]$. The taper datum $F$ carries the functions $\hat\varphi$, $\Phi$ and the constants $a, b$ of [eq:abdef], and the hypothesis `LocalHypsCoreW` packages the standing taper facts of the paper's Section 2.2 (the majorant bounds [eq:psidef], Poisson summation [lem:poisson], the Plancherel identities, etc.), without the cap $\lambda \le 1$. The seam form is $\mathcal{M}[u_1, u_2] = \iint_{I \times I} \Phi(\tau - \tau')^2 u_1(\tau) u_2(\tau')\, d\tau\, d\tau'$, and $\mathcal{M} = \mathcal{M}[\nu_X, \nu_X]$ where the density $\nu_X = \mu + \Pi_X + P_X$ [eq:nudef] splits into the archimedean part $\mu$ (a digamma expression, [eq:mudef]), the pole part $\Pi_X$ [eq:Pidef], and the prime sum $P_X(\tau) = -\tfrac1\pi \sum_{n \le X} \Lambda(n) n^{-1/2} \cos(\tau \log n)$ [eq:Pdef]. Assuming the $\Gamma$-facts H-Γ (which give continuity of $\mu$) and the window-generic taper facts `LocalHypsCore`, the theorem asserts the exact identity [eq:Msplit] of Section 5.4:
--   $$\mathcal{M} \;=\; \mathcal{M}[\mu,\mu] + \mathcal{M}[P_X,P_X] + 2\,\mathcal{M}[\mu,P_X] + 2\,\mathcal{M}[\mu,\Pi_X] + 2\,\mathcal{M}[P_X,\Pi_X] + \mathcal{M}[\Pi_X,\Pi_X].$$
--   The identity is valid because $\mathcal{M}[\cdot,\cdot]$ is a symmetric bilinear form ($\Phi^2$ is even) and all six densities are continuous on the compact square $I \times I$, so every integral is a genuine Lebesgue integral.
--
--   It is the `Msplit` field of `concreteFacts`: the splitting reduces the evaluation of $\mathcal{M}$ in [thm:traces] to the six separate estimates [prop:mumu], [prop:PP] and the four cross terms [prop:cross].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA.lean#L376-L389, docstring tag [eq:Msplit]

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.eq_Msplit (hΓ : Zeta23.GammaFacts) (p : Setting) (F : LocalFun) (hF : LocalHypsCore cϱ p F) :
    MtotalA p F =
      Mform F.Phi p.T Zeta23.mu Zeta23.mu + Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PX p.X)
        + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X) + 2 * Mform F.Phi p.T Zeta23.mu (Zeta23.PiX p.X)
        + 2 * Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)
        + Mform F.Phi p.T (Zeta23.PiX p.X) (Zeta23.PiX p.X) := by sorry
