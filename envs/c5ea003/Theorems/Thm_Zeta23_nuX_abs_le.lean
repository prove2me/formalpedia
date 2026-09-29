-- Prove2me | Theorems.Thm_Zeta23_nuX_abs_le
-- name    : Zeta23.nuX_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:20:51.609873+00:00
-- url     : https://prove2.me/theorems/ebfaea0e-78cc-4655-bea1-c1cb48b832ec
-- title:
--   Pointwise bound $|\nu_X(\tau)| \le B + \log^+\!\big(|\tau|/4T\big)$ with $B = l + 4\sqrt{X}$
-- statement:
--   Here $\nu_X = \mu + \Pi_X + P_X$ is the total density of [eq:nudef]: $\mu$ the archimedean (digamma) density, $\Pi_X$ the pole term, and $P_X(\tau) = -\frac{1}{\pi}\sum_{n \le X} \Lambda(n)\, n^{-1/2} \cos(\tau \log n)$ the prime term. The parameter is $X = e^{\lambda\, l(T)}$ with $l(T) = \log(T/2\pi)$ and a fixed exponent $\lambda > 0$; $\log^+ y = \max(\log y, 0)$.
--
--   Assuming the $\Gamma$-facts package H-Γ (`GammaFacts`: Stirling-type asymptotics for $\mu$), the assertion is: there exists $T_0 \ge 1$ such that for all $T \ge T_0$ and **all** real $\tau$,
--   $$\big|\nu_X(\tau)\big| \;\le\; \Big(l(T) + 4\sqrt{X}\Big) \;+\; \max\!\Big(\log\frac{|\tau|}{4T},\, 0\Big),$$
--   i.e. the paper's [eq:Bdef] bound with $B := l + 4\sqrt{X}$: a constant bound $B$ on $|\tau| \le 4T$, growing only logarithmically beyond. The Chebyshev–Mertens input controlling $\sum_{n \le X} \Lambda(n)/\sqrt{n} \ll \sqrt{X}$ is the fully proved `Zeta23.Cheb.chebyshevMertens`; only H-Γ is a hypothesis here (discharged elsewhere in the repository).
--
--   This pointwise control of the density $\nu_X$ is what makes the prime-side trace integrals absolutely convergent with acceptable error; from `Zeta23.PiFacts` it is consumed by `Zeta23.PrimeSide.lem_ends`, the endpoint estimate of the trace computation.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PiFacts.lean#L207-L406, docstring tag [eq:Bdef]

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

open Zeta23
open Real
set_option maxHeartbeats 1000000

theorem Zeta23.nuX_abs_le (hΓ : GammaFacts) {lam : ℝ} (hlam0 : 0 < lam) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T, T₀ ≤ T → ∀ τ : ℝ,
      |nuX (Real.exp (lam * l T)) τ|
        ≤ (l T + 4 * Real.sqrt (Real.exp (lam * l T)))
          + max (Real.log (|τ| / (4 * T))) 0 := by sorry
