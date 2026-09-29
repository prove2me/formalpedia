-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_W1b
-- name    : Zeta23.PrimeSide.W1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:08:45.386168+00:00
-- url     : https://prove2.me/theorems/6b9d29de-ea37-477d-ab12-ccb58e23f554
-- title:
--   (W1b) $\int_1^T \psi(u)^2(1+u)^2\,du \le 4\,(c_\varrho/w)^2$
-- statement:
--   Here $\psi(u) = \min\bigl(L,\ 2/|u|,\ c_\varrho/(wu^2)\bigr)$ is the taper majorant [eq:psidef] of the setting $p$ (window length $L$, ramp width $w$, profile constant $c_\varrho$), assumed to satisfy the window-generic package `LocalHypsCoreW`, and $T$ is the height, with $T \ge 1$.
--
--   The theorem is the leaf integral
--   $$\int_1^{T} \psi(u)^2\,(1+u)^2\,du \;\le\; 4\Bigl(\frac{c_\varrho}{w}\Bigr)^2 :$$
--   on $[1,T]$ one has $\psi(u) \le c_\varrho/(wu^2)$ and $(1+u)^2 \le 4u^2$, so the integrand is at most $4(c_\varrho/w)^2 u^{-2}$, and $\int_1^T u^{-2}\,du \le 1$.
--
--   It is one of the weighted $\psi$-integrals (W1a–W1d) consumed by `setIntegral_rho_div_gwt_le` in the boundary-weight ("ends") analysis of the second moment (module `Zeta23.PrimeSideA.EndsE1`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L74-L109

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

theorem Zeta23.PrimeSide.W1b (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) :
    ∫ u in (1:ℝ)..p.T, psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ 4 * (cϱ / p.w) ^ 2 := by sorry
