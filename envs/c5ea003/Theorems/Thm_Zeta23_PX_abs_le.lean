-- Prove2me | Theorems.Thm_Zeta23_PX_abs_le
-- name    : Zeta23.PX_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:56.114857+00:00
-- url     : https://prove2.me/theorems/9fb9b901-c74b-48eb-945c-c38f2146ac08
-- title:
--   Triangle-inequality bound $|P_X(\tau)| \le \frac{1}{\pi}\sum_{n \le X} \Lambda(n)/\sqrt{n}$
-- statement:
--   Let $P_X$ be the prime-side density of the explicit formula [eq:Pdef],
--   $$P_X(\tau) \;=\; -\frac{1}{\pi} \sum_{0 < n \le \lfloor X \rfloor} \frac{\Lambda(n)}{\sqrt{n}}\, \cos(\tau \log n),$$
--   where $\Lambda$ is the von Mangoldt function and the sum runs over the integers $n \in (0, \lfloor X \rfloor]$ (Lean's `Finset.Ioc 0 ⌊X⌋₊`, the same indexing as Mathlib's Chebyshev $\psi$). The theorem asserts, for all real $X$ and $\tau$, the triangle-inequality bound
--   $$|P_X(\tau)| \;\le\; \frac{1}{\pi} \sum_{0 < n \le \lfloor X \rfloor} \frac{\Lambda(n)}{\sqrt{n}},$$
--   obtained by bounding each $|\cos(\tau \log n)|$ by $1$.
--
--   In the module `Zeta23.PiFacts` this feeds `Zeta23.nuX_abs_le`, the pointwise bound $|\nu_X(\tau)| \le B + \log^+(|\tau|/4T)$ of [eq:Bdef] for the full density $\nu_X = \mu + \Pi_X + P_X$, once the Chebyshev–Mertens estimate $\sum_{n\le X} \Lambda(n)/\sqrt n \le 3\sqrt X$ is applied.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PiFacts.lean#L170-L187, docstring tag [eq:Pdef]

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
open ArithmeticFunction

theorem Zeta23.PX_abs_le (X τ : ℝ) :
    |PX X τ| ≤ (1 / Real.pi) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, vonMangoldt n / Real.sqrt n := by sorry
