-- Prove2me | Theorems.Thm_Complex_cpow_tendsto
-- name    : Complex.cpow_tendsto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:57:13.728063+00:00
-- url     : https://prove2.me/theorems/a39712e6-b5f1-4860-94d4-e2e10a76fddb
-- title:
--   $n^{1-s} \to 0$ as $n \to \infty$ for $\mathrm{Re}(s) > 1$
-- statement:
--   Let $s \in \mathbb{C}$ with $\mathrm{Re}(s) > 1$. Then
--   $$\lim_{n \to \infty} n^{\,1-s} = 0,$$
--   where $n$ ranges over the natural numbers (cast into $\mathbb{C}$) and $n^{1-s}$ is the principal complex power.
--
--   The exponent $1 - s$ has real part $1 - \mathrm{Re}(s) < 0$, and $|n^{1-s}| = n^{1 - \mathrm{Re}(s)}$ for $n \ge 1$, so the modulus decays polynomially to zero.
--
--   In the PNT+ zeta-bounds development this handles the leading Euler–Maclaurin boundary term $\tfrac{N^{1-s}}{s-1}$ in the truncated representation of $\zeta(s)$: for $\mathrm{Re}(s) > 1$ this term vanishes as the truncation point $N \to \infty$, identifying the truncated formula with the Dirichlet series.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L746-L752

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

theorem Complex.cpow_tendsto {s : ℂ} (s_re_gt : 1 < s.re) :
    Tendsto (fun (x : ℕ) ↦ (x : ℂ) ^ (1 - s)) atTop (𝓝 0) := by sorry
