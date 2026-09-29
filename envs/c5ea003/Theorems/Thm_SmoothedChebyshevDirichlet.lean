-- Prove2me | Theorems.Thm_SmoothedChebyshevDirichlet
-- name    : SmoothedChebyshevDirichlet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:03:01.506762+00:00
-- url     : https://prove2.me/theorems/edd473b9-e654-4afe-af58-3bc5fb0d2daf
-- title:
--   Contour-integral representation of the smoothed Chebyshev function as a smoothed Dirichlet sum
-- statement:
--   Let $F$ be a smoothing kernel of class $C^1$, nonnegative on $(0,\infty)$, supported in $[1/2, 2]$, and of multiplicative mass one $\int_0^\infty F(x)\,dx/x = 1$. Fix $X > 3$ and $\epsilon \in (0, 1)$. The smoothed Chebyshev function $\psi_\epsilon(X) = \mathrm{SmoothedChebyshev}\,F\,\epsilon\,X$ is defined by the vertical-line contour integral
--
--   $$\psi_\epsilon(X) \;=\; \frac{1}{2\pi i} \int_{(\sigma)} \left( -\frac{\zeta'}{\zeta}(s) \right) \mathcal{M}\big(\widetilde{1_\epsilon}\big)(s)\, X^s \, ds,$$
--
--   where $\sigma > 1$, $\widetilde{1_\epsilon}$ is the smoothed cutoff built from $F$, and $\mathcal{M}$ denotes the Mellin transform.
--
--   The theorem asserts that this contour integral evaluates to the smoothed von Mangoldt sum:
--
--   $$\psi_\epsilon(X) \;=\; \sum_{n = 1}^{\infty} \Lambda(n)\, \widetilde{1_\epsilon}\!\left(\frac{n}{X}\right).$$
--
--   This is the Perron / Mellin-inversion step of the smoothed Prime Number Theorem proof: expanding $-\zeta'/\zeta$ into its Dirichlet series $\sum \Lambda(n) n^{-s}$ on the line $\mathrm{Re}(s) = \sigma > 1$, interchanging sum and integral, and applying Mellin inversion to each term recovers the smoothed cutoff evaluated at $n/X$. It converts the arithmetic object (a weighted prime-power sum) into an analytic one (a contour integral), which can then be shifted into the zero-free region of $\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean#L189-L285

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow
set_option backward.isDefEq.respectTransparency false

theorem SmoothedChebyshevDirichlet {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), SmoothingF x / x = 1)
    {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) :
    SmoothedChebyshev SmoothingF ε X =
      ∑' n, ArithmeticFunction.vonMangoldt n * Smooth1 SmoothingF ε (n / X) := by sorry
