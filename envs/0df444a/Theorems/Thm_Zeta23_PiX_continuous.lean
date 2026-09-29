-- Prove2me | Theorems.Thm_Zeta23_PiX_continuous
-- name    : Zeta23.PiX_continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:57:22.400857+00:00
-- url     : https://prove2.me/theorems/b33ae41a-3ffb-4c11-8264-c210a0cf7037
-- title:
--   Continuity of $\tau \mapsto \Pi_X(\tau)$
-- statement:
--   Let $\Pi_X$ be the pole-term density [eq:Pidef],
--   $$\Pi_X(\tau) \;=\; \frac{1}{2\pi(\tfrac14+\tau^2)} \;+\; \frac{1}{\pi}\,\mathrm{Re}\,\frac{X^{s}-1}{s}, \qquad s = \tfrac12 + i\tau.$$
--   The theorem asserts that for every real $X > 0$, the function $\tau \mapsto \Pi_X(\tau)$ is continuous on $\mathbb{R}$ (Lean's `Continuous (PiX X)`). Note that $s = \tfrac12 + i\tau$ never vanishes, so the quotient $(X^s-1)/s$ is continuous in $\tau$ without any removable-singularity issue.
--
--   This is an integrability input: in the module `Zeta23.PiFacts` it is consumed by `Zeta23.PrimeSide.localHyps_concrete`, which verifies the concrete local hypotheses (continuity, local integrability) needed for the prime-side integral computations.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PiFacts.lean#L135-L153

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

theorem Zeta23.PiX_continuous {X : ℝ} (hX : 0 < X) : Continuous (PiX X) := by sorry
