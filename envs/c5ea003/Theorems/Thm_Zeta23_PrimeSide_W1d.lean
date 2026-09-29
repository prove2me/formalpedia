-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_W1d
-- name    : Zeta23.PrimeSide.W1d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:09:49.993293+00:00
-- url     : https://prove2.me/theorems/6da59402-5d1a-49e9-9f6b-c61ddb82126d
-- title:
--   (W1d) $\int_1^T J(u)(1+u)^2\,du \le \tfrac43(c_\varrho/w)^2\log T$
-- statement:
--   Here $\psi$ is the taper majorant [eq:psidef] of the setting $p$ (ramp width $w$, profile constant $c_\varrho$, height $T \ge 1$), assumed to satisfy the window-generic package `LocalHypsCoreW`, and $J(u) := \int_{(u,\infty)}\psi(r)^2\,dr$ is its tail integral.
--
--   The theorem is the leaf integral
--   $$\int_1^{T} J(u)\,(1+u)^2\,du \;\le\; \frac43\Bigl(\frac{c_\varrho}{w}\Bigr)^2 \log T :$$
--   for $u \ge 1$ the bound $\psi(r) \le c_\varrho/(wr^2)$ gives $J(u) \le (c_\varrho/w)^2/(3u^3)$, while $(1+u)^2 \le 4u^2$ on $[1,T]$, so the integrand is at most $\tfrac43(c_\varrho/w)^2 u^{-1}$ and the integral of $u^{-1}$ is $\log T$.
--
--   It is one of the weighted $\psi$-integrals (W1a–W1d) consumed by `setIntegral_rho_div_gwt_le` in the boundary-weight ("ends") analysis of the second moment (module `Zeta23.PrimeSideA.EndsE1`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L136-L161

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

theorem Zeta23.PrimeSide.W1d (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) :
    ∫ u in (1:ℝ)..p.T, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T := by sorry
