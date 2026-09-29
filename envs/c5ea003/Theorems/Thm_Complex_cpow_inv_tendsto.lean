-- Prove2me | Theorems.Thm_Complex_cpow_inv_tendsto
-- name    : Complex.cpow_inv_tendsto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:56:47.100473+00:00
-- url     : https://prove2.me/theorems/58555ec5-8924-4649-b3d2-b4f9f7971b3c
-- title:
--   $n^{-s} \to 0$ as $n \to \infty$ for $\mathrm{Re}(s) > 0$
-- statement:
--   Let $s \in \mathbb{C}$ with $\mathrm{Re}(s) > 0$. Then the reciprocal complex powers of the natural numbers tend to zero:
--   $$\lim_{n \to \infty} \frac{1}{n^{s}} = 0,$$
--   where $n$ ranges over the natural numbers (cast into $\mathbb{C}$), the limit is along the cofinite filter at infinity ($n \to \infty$), and $n^s$ denotes the principal complex power.
--
--   Since $|n^s| = n^{\mathrm{Re}(s)}$ for $n \ge 1$, the hypothesis $\mathrm{Re}(s) > 0$ makes the modulus of $n^s$ grow without bound, so its inverse tends to $0$.
--
--   This limit is used in the ZetaBounds development when passing to the limit $N \to \infty$ in truncated Euler–Maclaurin representations of $\zeta(s)$ and $\zeta'(s)$: the boundary terms carrying factors $N^{-s}$ disappear precisely because of this lemma.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L754-L759

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

theorem Complex.cpow_inv_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun (x : ℕ) ↦ ((x : ℂ) ^ s)⁻¹) atTop (𝓝 0) := by sorry
