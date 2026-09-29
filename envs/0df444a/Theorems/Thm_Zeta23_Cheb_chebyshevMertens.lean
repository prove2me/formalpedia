-- Prove2me | Theorems.Thm_Zeta23_Cheb_chebyshevMertens
-- name    : Zeta23.Cheb.chebyshevMertens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:44:19.981125+00:00
-- url     : https://prove2.me/theorems/456298b2-160f-4504-b339-0fb51deb0bcf
-- title:
--   The Chebyshev–Mertens package (H-cheb) holds unconditionally
-- statement:
--   The hypothesis structure `ChebyshevMertens` of `Zeta23/Hypotheses.lean` bundles the paper's [lem:cheb]: the elementary Chebyshev–Mertens estimates for the von Mangoldt function $\Lambda$. Its fields state, with all sums over $1 \le n \le \lfloor x\rfloor$:
--   $$\sum_{n \le x} \Lambda(n) \ll x, \qquad \sum_{n \le x} \frac{\Lambda(n)}{\sqrt n} \le 3\sqrt x \ (x \ge x_0), \qquad \sum_{n \le x} \frac{\Lambda(n)}{\sqrt n \log n} \ll \frac{\sqrt x}{\log x}, \qquad \sum_{n \le x} \Lambda(n)^2 \ll x \log x \quad \text{[eq:cheb1]},$$
--   $$\sum_{n \le x} \frac{\Lambda(n)^2}{n} = \frac{(\log x)^2}{2} + O(\log x), \qquad \sum_{n \le x} \frac{\Lambda(n)^2}{n}(\log x - \log n) = \frac{(\log x)^3}{6} + O((\log x)^2) \quad \text{[eq:cheb2]},$$
--   each $\ll$/$O(\cdot)$ being an explicit existential constant, for $x \ge 2$ (in the third sum Lean's convention $0/0 = 0$ handles $n = 1$).
--
--   The theorem asserts that this entire package holds — unconditionally, with no unproved input: the proof combines Mathlib's Chebyshev bound for $\psi(x)$, Abel summation, and the Mertens-type theorem of `Zeta23/FromPNTPlus/Mertens.lean`.
--
--   These estimates are the arithmetic input to the prime side of the argument: they control the density $\nu_X$ (via `nuX_abs_le`) and the mollified trace computations, and the package is consumed directly by the headline theorems `thmA3` and `thmA3_cumulative`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Chebyshev.lean#L1192-L1206, docstring tag [lem:cheb]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
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
open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime
open MeasureTheory

theorem Zeta23.Cheb.chebyshevMertens : ChebyshevMertens := by sorry
