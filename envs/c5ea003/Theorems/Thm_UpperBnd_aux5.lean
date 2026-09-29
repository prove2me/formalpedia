-- Prove2me | Theorems.Thm_UpperBnd_aux5
-- name    : UpperBnd_aux5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:04:58.269927+00:00
-- url     : https://prove2.me/theorems/91a3cde1-6319-4b4a-a1d8-baadc22914b0
-- title:
--   Floor-ratio power bound: $(|t| / \lfloor|t|\rfloor)^{\sigma} \le 4$ for $|t| > 3$, $\sigma \le 2$
-- statement:
--   Let $\sigma, t$ be real numbers with $|t| > 3$ and $\sigma \le 2$. Then
--   $$\left( \frac{|t|}{\lfloor |t| \rfloor} \right)^{\sigma} \le 4,$$
--   where $\lfloor |t| \rfloor$ denotes the natural-number floor of $|t|$.
--
--   This is a small technical lemma used when passing between estimates phrased in terms of the continuous parameter $|t|$ and those phrased in terms of the integer truncation point $N = \lfloor |t| \rfloor$ in Euler-Maclaurin expansions of $\zeta$. Since $|t| > 3$, the ratio $|t|/\lfloor|t|\rfloor$ is less than $2$, so raising it to any exponent $\sigma \le 2$ costs at most a factor of $4$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1333-L1337

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

theorem UpperBnd_aux5 {σ t : ℝ} (t_ge : 3 < |t|) (σ_le : σ ≤ 2) : (|t| / ⌊|t|⌋₊) ^ σ ≤ 4 := by sorry
