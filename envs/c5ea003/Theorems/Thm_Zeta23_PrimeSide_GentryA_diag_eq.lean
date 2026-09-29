-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_GentryA_diag_eq
-- name    : Zeta23.PrimeSide.GentryA_diag_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:00:43.988038+00:00
-- url     : https://prove2.me/theorems/f1a92fcd-a9f3-4b47-8211-b8d2d1a250a5
-- title:
--   Decomposition of a diagonal Gram entry along $\nu_X = \mu + \Pi_X + P_X$
-- statement:
--   The prime-side Gram matrix has entries $G_{kl} = \int_{\mathbb R}\hat\varphi(\tau-\tau_k)\,\hat\varphi(\tau-\tau_l)\,\nu_X(\tau)\,d\tau$ (`GentryA`), where $\nu_X = \mu + \Pi_X + P_X$ is the zero-density surrogate of [eq:nudef]: $\mu$ is the archimedean density built from $\Gamma'/\Gamma$ [eq:mudef], $\Pi_X$ the pole term [eq:Pidef], and $P_X(\tau) = -\tfrac1\pi\sum_{n\le X}\Lambda(n)n^{-1/2}\cos(\tau\log n)$ the prime-power sum [eq:Pdef]. Assume the Stirling-type facts H-$\Gamma$ (`GammaFacts`) for $\mu$, the window-generic taper package `LocalHypsCore`, and let $k \in \mathbb Z$ with $\tau_k > 0$.
--
--   Then, after the translation $\tau = \tau_k + r$, the diagonal entry splits into its $\mu$-, $\Pi$- and $P$-parts:
--   $$G_{kk} \;=\; \int_{\mathbb R}\hat\varphi(r)^2\,\mu(\tau_k+r)\,dr \;+\; \int_{\mathbb R}\hat\varphi(r)^2\,\Pi_X(\tau_k+r)\,dr \;+\; \int_{\mathbb R}\hat\varphi(r)^2\,P_X(\tau_k+r)\,dr,$$
--   as in §5.2's $G_{kk} = G^\mu_{kk} + G^\Pi_{kk} + G^P_{kk}$.
--
--   The three pieces are then estimated separately (Riemann-sum comparison for $\mu$, `Pi_part_bound`, `sum_P_part_bound`) in `prop_trace_mu`, the trace asymptotics [prop:trace] of the mollified second-moment argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1269-L1291, docstring tag [eq:nudef]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.GentryA_diag_eq (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (k : ℤ)
    (hk : 0 < p.tau k) :
    GentryA p F k k = (∫ r, F.phiHat r ^ 2 * Zeta23.mu (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (p.tau k + r))
      + (∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)) := by sorry
