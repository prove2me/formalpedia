-- Prove2me | Theorems.Thm_mul_le_mul_triple
-- name    : mul_le_mul_triple
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:43:01.610634+00:00
-- url     : https://prove2.me/theorems/1698c60b-a060-4899-8471-3986e24352ba
-- title:
--   Monotonicity of a triple product: $a \le b$, $c \le d$, $e \le f$ implies $ace \le bdf$
-- statement:
--   Let $\alpha$ be a type equipped with a multiplication with zero (`MulZeroClass`), a preorder, and the compatibility assumptions that multiplication by nonnegative elements on either side is monotone (`PosMulMono` and `MulPosMono`). Let $a, b, c, d, e, f \in \alpha$ satisfy $a \le b$, $c \le d$, $e \le f$, together with the positivity side conditions $0 \le c$, $0 \le b$, and $0 \le e$. Then
--
--   $$a \cdot c \cdot e \;\le\; b \cdot d \cdot f.$$
--
--   This is the three-factor analogue of the standard two-factor inequality `mul_le_mul`: one may multiply three inequalities between nonnegative-flavored quantities termwise. In the PNT+ development it is a convenience lemma used repeatedly when assembling products of three separate bounds (for instance in the $3$-$4$-$1$ zeta product estimates and other multi-factor norm bounds), avoiding nested applications of the binary lemma.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1212-L1215

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

theorem mul_le_mul_triple {α : Type*} {a b c d e f : α} [MulZeroClass α] [Preorder α] [PosMulMono α]
    [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (h₃ : e ≤ f) (c0 : 0 ≤ c) (b0 : 0 ≤ b)
    (e0 : 0 ≤ e) : a * c * e ≤ b * d * f := by sorry
