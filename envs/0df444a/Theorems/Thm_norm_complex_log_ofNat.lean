-- Prove2me | Theorems.Thm_norm_complex_log_ofNat
-- name    : norm_complex_log_ofNat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:03:01.083883+00:00
-- url     : https://prove2.me/theorems/f2d7475a-c0b3-437b-9e8e-4909e79f6a68
-- title:
--   Norm of the complex logarithm of a natural number: $\|\log n\| = \log n$
-- statement:
--   For every natural number $n$, the complex logarithm of $n$ (viewed as a complex number) has norm equal to the real logarithm of $n$:
--
--   $$\bigl\| \log_{\mathbb{C}}(n) \bigr\| \;=\; \log_{\mathbb{R}}(n).$$
--
--   Since $n \ge 0$ is real and nonnegative, its principal complex logarithm is real with no imaginary part, and for $n \ge 1$ it is nonnegative, so its norm (absolute value) is exactly $\log n$. (The degenerate case $n = 0$ holds as well because both sides are $0$ under the Lean conventions $\log 0 = 0$.)
--
--   This small bridge lemma lets Dirichlet-series manipulations pass freely between the complex logarithm appearing in $n^{-s} = e^{-s \log n}$ and the real quantity $\log n$ appearing in the von Mangoldt function and in size estimates of terms such as $\Lambda(n)/n^s$. It is used throughout the bounds on $\zeta'/\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1417-L1421

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem norm_complex_log_ofNat (n : ℕ) : ‖(n : ℂ).log‖ = (n : ℝ).log := by sorry
