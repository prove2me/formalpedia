-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integral_Mnear_le
-- name    : Zeta23.PrimeSide.integral_Mnear_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:16:38.331535+00:00
-- url     : https://prove2.me/theorems/96ef712c-ba2d-4d8e-97da-a2f5d2968eab
-- title:
--   Near half-line integral of the majorant: $\int_0^{2T} M_{\mathrm{near}} \le B\,[\Psi' + \tfrac{L}{2\pi}(\Psi' + \tfrac{c_\varrho}{w}\log 2T)]$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $L=\lambda\log(T/2\pi)$, taper data $F$ satisfying the window-generic core hypotheses with profile constant $c_\varrho$, and majorant $\psi(r)=\min(L,\,2/|r|,\,c_\varrho/(w r^2))$. For a level $B$, the near majorant (§5.3), for a distance $\Delta$ from the window $I=[T,2T]$, is
--   $$M_{\mathrm{near}}(\Delta)\ :=\ B\Bigl(\psi(\Delta)+\frac{L}{2\pi}\min\bigl(\Psi',\ \tfrac{c_\varrho}{w\Delta}\bigr)\Bigr),\qquad \Psi':=\int_0^\infty\psi(r)\,dr.$$
--
--   Assume $B\ge 0$ and $T\ge 1$. Then
--   $$\int_0^{2T} M_{\mathrm{near}}(\Delta)\,d\Delta\ \le\ B\Bigl[\Psi'+\frac{L}{2\pi}\Bigl(\Psi'+\frac{c_\varrho}{w}\log(2T)\Bigr)\Bigr],$$
--   the integral on the left being taken over the half-open interval $(0,2T]$.
--
--   This is the near-range half of the grid bound N2 of §5.3 (module `Zeta23.PrimeSideA.EndsNu`); together with `integral_Mfar_le` it yields `nu_grid_bound_raw`, the raw form of the bound $\int_{\tau\notin I}|\nu|\,\sigma\ll BLl$ used in the $\mathcal{E}_2$ part of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L458-L522

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
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.integral_Mnear_le (hF : LocalHypsCoreW cϱ p F) (hB : 0 ≤ B) (hT : 1 ≤ p.T) :
    ∫ Δ in Ioc 0 (2 * p.T), Mnear cϱ p B Δ
      ≤ B * ((∫ r in Ioi 0, psiA cϱ p r)
        + p.L / (2 * π) * ((∫ r in Ioi 0, psiA cϱ p r) + cϱ / p.w * Real.log (2 * p.T))) := by sorry
