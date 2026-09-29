-- Prove2me | Theorems.Thm_Zeta23_WeilEF_EF_lit_zeta
-- name    : Zeta23.WeilEF.EF_lit_zeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:34.47124+00:00
-- url     : https://prove2.me/theorems/42b13390-99ec-44ba-9f23-a441125132b9
-- title:
--   The Weil explicit formula for $\zeta$, literature form [eq:EFstd]
-- statement:
--   This node establishes the literature form of the Weil explicit formula for Mathlib's Riemann zeta function `riemannZeta`. The hypothesis `ZetaSeam` is a bundle of classical seam facts about the nontrivial zeros of $\zeta$ (each zero has finite analytic order $\ge 1$; the reflection $\rho \mapsto 1-\bar\rho$ preserves the zero set and the multiplicities; there are finitely many nontrivial zeros in each horizontal window $T_1 < \gamma \le T_2$), which lets the nontrivial zeros with multiplicities $m_\rho := $ `analyticOrderAt` be packaged as the abstract zero configuration `zetaZeros hs`.
--
--   The conclusion is `Zeta23.EF.EF_lit (zetaZeros hs)`: for every test function $k \in C_c^2(\mathbb{R}, \mathbb{C})$, writing $h(z) := \hat k(z) = \int_{\mathbb{R}} k(u)e^{izu}du$ and $\gamma_\rho := (\rho - 1/2)/i$, the zero sum $\sum_\rho m_\rho\, h(\gamma_\rho)$ over the distinct nontrivial zeros converges absolutely and
--   $$\sum_{\rho} m_\rho\, h(\gamma_\rho) \;=\; h\big(\tfrac{i}{2}\big) + h\big(-\tfrac{i}{2}\big) \;-\; \sum_{n \ge 1} \frac{\Lambda(n)}{\sqrt{n}}\big(k(\log n) + k(-\log n)\big) \;+\; \frac{1}{2\pi}\int_{\mathbb{R}} h(r)\left[\operatorname{Re}\frac{\Gamma'}{\Gamma}\!\left(\frac14 + \frac{ir}{2}\right) - \log\pi\right] dr,$$
--   where $\Lambda$ is the von Mangoldt function. The proof assembles the full-line contour identity: the $\zeta$-part gives the prime sum, the $\Gamma_{\mathbb{R}}$-part gives the archimedean integral, the pole terms at $s = 0, 1$ give $h(\pm i/2)$, and the summability clause is `EF_zero_sum_summable`.
--
--   This is the arithmetic heart of the project: together with `Zeta23.EF.explicitFormulaPaper_of_lit` it discharges the explicit-formula hypothesis H-EF, and it is consumed directly by `Zeta23.thmA0` and `Zeta23.thmA0_cumulative`, the nodes proving Theorem A (more than $2/3 - \varepsilon$ of the zeros on the critical line) unconditionally.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/WeilEF/Main.lean#L40-L266

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

open Zeta23
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem Zeta23.WeilEF.EF_lit_zeta (hs : ZetaSeam) : Zeta23.EF.EF_lit (zetaZeros hs) := by sorry
