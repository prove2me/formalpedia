-- Prove2me | Theorems.Thm_DerivUpperBnd_aux2
-- name    : DerivUpperBnd_aux2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:06:50.627822+00:00
-- url     : https://prove2.me/theorems/8e3a1d7f-f1e3-40a6-be10-533f849dae99
-- title:
--   Euler–Maclaurin boundary term $N^{1-s}/(1-s)^2$ is $O(e^A)$ for $|t| > 3$
-- statement:
--   Let $A, \sigma, t$ be real with $|t| > 3$ and $\sigma \in \big[1 - A/\log|t|,\, 2\big]$. Set $N = \lfloor |t| \rfloor$ and $s = \sigma + it$, and assume $N > 0$, $N \le |t|$, $s \neq 1$, and $\sigma > 1/2$. Then the second-order boundary term of the Euler–Maclaurin expansion for $\zeta'$ obeys
--   $$\Big\| \frac{-N^{\,1-s}}{(1-s)^{2}} \Big\| \;\le\; e^{A} \cdot 2 \cdot \frac{1}{3}.$$
--
--   The modulus of the numerator is $N^{1-\sigma} \le |t|^{A/\log|t|} = e^{A}$ in the given range of $\sigma$, while $|1-s| \ge |t| > 3$ makes the denominator at least $9$; the stated constant $2/3$ leaves comfortable room.
--
--   This is one of the finitely many boundary-term estimates that together bound the derivative of the truncated zeta representation, yielding the classical bound $|\zeta'(\sigma+it)| \ll \log^2 |t|$ near the edge of the critical strip, an input to the zero-free region and the PNT error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1485-L1504

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

theorem DerivUpperBnd_aux2 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 →
    1 / 2 < σ → ‖-↑N ^ (1 - s) / (1 - s) ^ 2‖ ≤ A.exp * 2 * (1 / 3) := by sorry
