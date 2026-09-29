-- Prove2me | Theorems.Thm_Zeta23_PiX_abs_le
-- name    : Zeta23.PiX_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:57:16.943627+00:00
-- url     : https://prove2.me/theorems/28e2e844-139b-4ddb-b041-b60985d5807c
-- title:
--   Decay bound $|\Pi_X(\tau)| \le 3\sqrt{X}/(1+|\tau|)$
-- statement:
--   Let $\Pi_X$ be the pole-term density of the explicit formula [eq:Pidef],
--   $$\Pi_X(\tau) \;=\; \frac{1}{2\pi\bigl(\tfrac14 + \tau^2\bigr)} \;+\; \frac{1}{\pi}\,\mathrm{Re}\,\frac{X^{s} - 1}{s}, \qquad s = \tfrac12 + i\tau,$$
--   the density rewriting of the terms coming from the pole of $\zeta$ at $s=1$. The theorem asserts: for every real $X \ge 1$ and every real $\tau$,
--   $$|\Pi_X(\tau)| \;\le\; \frac{3\sqrt{X}}{1 + |\tau|}.$$
--   The numerator reflects $|X^s| = \sqrt X$ on the line $\mathrm{Re}\,s = 1/2$, and the denominator the decay $1/|s| \ll 1/(1+|\tau|)$; the constant $3$ is explicit.
--
--   In the module `Zeta23.PiFacts` this bound feeds both `Zeta23.PrimeSide.localHyps_concrete` (integrability/local hypotheses on the prime side) and `Zeta23.nuX_abs_le`, the pointwise bound of [eq:Bdef] for the full density $\nu_X = \mu + \Pi_X + P_X$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PiFacts.lean#L29-L127

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

open Zeta23
open Real

theorem Zeta23.PiX_abs_le {X : ℝ} (hX : 1 ≤ X) (τ : ℝ) :
    |PiX X τ| ≤ 3 * Real.sqrt X / (1 + |τ|) := by sorry
