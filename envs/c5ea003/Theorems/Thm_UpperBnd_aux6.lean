-- Prove2me | Theorems.Thm_UpperBnd_aux6
-- name    : UpperBnd_aux6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:06:24.53907+00:00
-- url     : https://prove2.me/theorems/fda5133d-65af-409c-ab8c-1c1ab1867a55
-- title:
--   Comparison of floor powers $\lfloor|t|\rfloor^{1-\sigma}$, $\lfloor|t|\rfloor^{-\sigma}$ with powers of $|t|$ in the strip $\tfrac12 < \sigma \le 2$
-- statement:
--   Let $\sigma, t$ be real numbers with $|t| > 3$ and $\sigma \in (\tfrac12, 2]$, and suppose $\sigma + it \ne 1$. Write $N = \lfloor |t| \rfloor$ for the natural-number floor of $|t|$, and assume $0 < N$ and $N \le |t|$. Then the following three estimates hold simultaneously:
--   $$\frac{N^{1-\sigma}}{\|1 - (\sigma + it)\|} \le 2\,|t|^{1-\sigma}, \qquad \frac{N^{-\sigma}}{2} \le |t|^{1-\sigma}, \qquad \frac{N^{-\sigma}}{\sigma} \le 8\,|t|^{-\sigma}.$$
--
--   These are the bookkeeping estimates needed to convert the boundary terms of the truncated Euler-Maclaurin representation $\zeta_0(N, s)$ (which are naturally expressed in terms of the integer cutoff $N$) into clean bounds in terms of $|t|$ alone. The first uses $\|1 - s\| \ge |t| \ge N/2$-type comparisons, and the last two exploit $N \le |t| \le 2N$ together with $\sigma \le 2$. They are consumed in the proof of the upper bound $|\zeta(\sigma+it)| \ll \log|t|$ near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1339-L1362

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

theorem UpperBnd_aux6 {σ t : ℝ} (t_ge : 3 < |t|) (hσ : σ ∈ Ioc (1 / 2) 2)
    (neOne : σ + t * I ≠ 1) (Npos : 0 < ⌊|t|⌋₊) (N_le_t : ⌊|t|⌋₊ ≤ |t|) :
    ⌊|t|⌋₊ ^ (1 - σ) / ‖1 - (σ + t * I)‖ ≤ |t| ^ (1 - σ) * 2 ∧
    ⌊|t|⌋₊ ^ (-σ) / 2 ≤ |t| ^ (1 - σ) ∧ ⌊|t|⌋₊ ^ (-σ) / σ ≤ 8 * |t| ^ (-σ) := by sorry
