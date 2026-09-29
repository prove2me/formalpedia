-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Mnear_integrableOn
-- name    : Zeta23.PrimeSide.Mnear_integrableOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:04:54.349909+00:00
-- url     : https://prove2.me/theorems/0de441b0-8a17-4bd7-a034-36ad631b14b6
-- title:
--   Integrability of the near-range majorant $M_{\mathrm{near}}$ on $(0, 2T]$
-- statement:
--   Here $\psi(r) = \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ (with $\psi(0) := L$) is the taper majorant [eq:psidef], and for a bound $B$ on the density the near-range majorant of §5.3 is
--   $$M_{\mathrm{near}}(\Delta) \;=\; B\Bigl(\psi(\Delta) + \frac{L}{2\pi}\,\min\Bigl(\int_0^\infty \psi,\ \frac{c_\varrho}{w\Delta}\Bigr)\Bigr).$$
--   Assume `LocalHypsCoreW` (the window-generic taper package without the bandwidth cap $\lambda \le 1$) and $T > 0$. Then $\Delta \mapsto M_{\mathrm{near}}(\Delta)$ is integrable on the interval $(0, 2T]$.
--
--   This supplies the dominating function for the boundary ("ends") estimates of [lem:ends]: it is consumed by `integrableOn_sigma_mul_abs_nuX` and `nu_grid_bound_raw`, which dominate the grid sum $\sigma(\tau) = \sum_k \psi(\tau - \tau_k)$ times the density $\nu_X$ near the window edges (module `Zeta23.PrimeSideA.EndsNu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L397-L414

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

theorem Zeta23.PrimeSide.Mnear_integrableOn (hF : LocalHypsCoreW cϱ p F) (_hT : 0 < p.T) :
    IntegrableOn (Mnear cϱ p B) (Ioc 0 (2 * p.T)) := by sorry
