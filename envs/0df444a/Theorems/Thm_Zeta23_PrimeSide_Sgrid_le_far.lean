-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Sgrid_le_far
-- name    : Zeta23.PrimeSide.Sgrid_le_far
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:07:42.178178+00:00
-- url     : https://prove2.me/theorems/37336435-c16e-4e0e-b2fb-95496b1e04af
-- title:
--   Far-range grid-sum bound: $S(\Delta) \le d\,\psi(\Delta)$
-- statement:
--   Here $\psi(r) = \min\bigl(L,\ 2/|r|,\ c_\varrho/(wr^2)\bigr)$ (with $\psi(0):=L$) is the taper majorant [eq:psidef], and $S(\Delta) := \sum_{j<d}\psi(\Delta + jh)$ (`Sgrid`) is the grid sum $\sigma(\tau) = \sum_{k<d}\psi(\tau - \tau_k)$ reduced to the half-line (§5.3), with $h = 2\pi/L$ the grid spacing and $d$ the grid size.
--
--   Under the window-generic package `LocalHypsCoreW` (no bandwidth cap $\lambda \le 1$), for every $\Delta \ge 0$:
--   $$S(\Delta) \;\le\; d\,\psi(\Delta),$$
--   since $\psi$ is antitone on $[0,\infty)$ and each grid shift only moves the argument to the right.
--
--   Together with the near-range bound $S(\Delta) \le \psi(\Delta) + h^{-1}\int_\Delta^\infty\psi$, it feeds the domination lemmas `dom_left` and `dom_right` for the boundary ("ends") estimates of [lem:ends] (module `Zeta23.PrimeSideA.EndsNu`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L254-L267

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

theorem Zeta23.PrimeSide.Sgrid_le_far (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    Sgrid cϱ p Δ ≤ p.d * psiA cϱ p Δ := by sorry
