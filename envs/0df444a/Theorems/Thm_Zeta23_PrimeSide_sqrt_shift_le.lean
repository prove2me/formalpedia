-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sqrt_shift_le
-- name    : Zeta23.PrimeSide.sqrt_shift_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:18:40.307464+00:00
-- url     : https://prove2.me/theorems/1491f0f3-1a68-47bc-b16a-e3bf8e820304
-- title:
--   Square-root shift inequality: $\sqrt{|a + r|/4T'} \le 1 + \sqrt{|r|/4T'}$
-- statement:
--   **Statement.** For real numbers $a, r, T'$ with $T' > 0$ and $|a| \le 4T'$,
--   $$\sqrt{\frac{|a + r|}{4T'}} \;\le\; 1 + \sqrt{\frac{|r|}{4T'}}.$$
--   Indeed $|a + r| \le 4T' + |r|$, and $\sqrt{x + y} \le \sqrt{x} + \sqrt{y}$.
--
--   **Role.** An elementary leaf inequality in the weighted-tail module `EndsWeighted`: it controls the sublogarithmic growth weight $\sqrt{|\tau|/4T}$ (which dominates $\log^+(|\tau|/4T)$ in the $\nu$-bound [eq:Bdef]) under shifts of the argument. Consumed by `Zeta23.PrimeSide.integrable_psiA_shift_mul_nu` (integrability of $\psi(\cdot - a)|\nu|$) and `Zeta23.PrimeSide.nu_weight_bound_of_L_le_two_B`, both part of the $\mathcal{E}_2$ tail estimates of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsWeighted.lean#L64-L77

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.sqrt_shift_le {a r T' : ℝ} (hT : 0 < T') (ha : |a| ≤ 4 * T') :
    Real.sqrt (|a + r| / (4 * T')) ≤ 1 + Real.sqrt (|r| / (4 * T')) := by sorry
