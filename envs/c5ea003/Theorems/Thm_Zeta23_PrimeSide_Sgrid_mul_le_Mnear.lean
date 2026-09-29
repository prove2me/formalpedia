-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Sgrid_mul_le_Mnear
-- name    : Zeta23.PrimeSide.Sgrid_mul_le_Mnear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:08:30.828781+00:00
-- url     : https://prove2.me/theorems/b3ae626d-4c86-49c3-9411-22d6914f5e4c
-- title:
--   Grid sum times density bound is dominated by $M_{\mathrm{near}}$
-- statement:
--   Here $S(\Delta) = \sum_{j<d}\psi(\Delta+jh)$ is the half-line grid sum of the taper majorant $\psi$ (§5.3), and the near-range majorant is
--   $$M_{\mathrm{near}}(\Delta) \;=\; B\Bigl(\psi(\Delta) + \frac{L}{2\pi}\min\Bigl(\int_0^\infty\psi,\ \frac{c_\varrho}{w\Delta}\Bigr)\Bigr),$$
--   where $B$ is a nonnegative bound for the density being integrated.
--
--   Under `LocalHypsCoreW`, for every $\Delta > 0$ and every $v$ with $0 \le v \le B$:
--   $$S(\Delta)\cdot v \;\le\; M_{\mathrm{near}}(\Delta),$$
--   combining the near-range bound $S(\Delta) \le \psi(\Delta) + h^{-1}\int_\Delta^\infty\psi$ (with $h^{-1} = L/2\pi$) with the two tail bounds $\int_\Delta^\infty\psi \le \int_0^\infty\psi$ and $\int_\Delta^\infty\psi \le c_\varrho/(w\Delta)$.
--
--   This is the pointwise domination step behind `dom_left` and `dom_right`, which control the window-edge ("ends") contributions in [lem:ends] (module `Zeta23.PrimeSideA.EndsNu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L321-L334

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

theorem Zeta23.PrimeSide.Sgrid_mul_le_Mnear (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) {v : ℝ} (hv0 : 0 ≤ v)
    (hv : v ≤ B) : Sgrid cϱ p Δ * v ≤ Mnear cϱ p B Δ := by sorry
