-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_W1c
-- name    : Zeta23.PrimeSide.W1c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:09:35.942441+00:00
-- url     : https://prove2.me/theorems/024e343a-f890-43da-8e20-c50a1437f2ea
-- title:
--   (W1c) $\int_0^1 J(u)(1+u)^2\,du \le 32\,L$ for the tail integral $J(u) = \int_u^\infty \psi^2$
-- statement:
--   Here $\psi$ is the taper majorant [eq:psidef] of the setting $p$ (window length $L$), assumed to satisfy the window-generic package `LocalHypsCoreW`, and $J(u) := \int_{(u,\infty)}\psi(r)^2\,dr$ is its tail integral.
--
--   The theorem is the leaf integral
--   $$\int_0^1 J(u)\,(1+u)^2\,du \;\le\; 32\,L :$$
--   the package's bound $\int_{\mathbb R}\psi^2 \le 8L$ gives $J(u) \le 8L$ for $u \ge 0$, and $(1+u)^2 \le 4$ on $[0,1]$.
--
--   It is one of the weighted $\psi$-integrals (W1a–W1d) consumed by `setIntegral_rho_div_gwt_le` in the boundary-weight ("ends") analysis of the second moment (module `Zeta23.PrimeSideA.EndsE1`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L118-L134

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

theorem Zeta23.PrimeSide.W1c (hF : LocalHypsCoreW cϱ p F) :
    ∫ u in (0:ℝ)..1, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2 ≤ 32 * p.L := by sorry
