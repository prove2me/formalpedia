-- Prove2me | Theorems.Thm_triv_bound_zeta
-- name    : triv_bound_zeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:46:14.330376+00:00
-- url     : https://prove2.me/theorems/5374e885-434e-43ae-8631-319ff9579e24
-- title:
--   Trivial bound for $-\zeta'/\zeta$ to the right of $\sigma = 1$: $\|(\zeta'/\zeta)(\sigma_0+it)\| \le (\sigma_0-1)^{-1} + C$
-- statement:
--   There exists a constant $C \ge 0$ such that for all real $\sigma_0$ and $t$ with $\sigma_0 > 1$,
--
--   $$\left\| -\frac{\zeta'}{\zeta}(\sigma_0 + it) \right\| \;\le\; \frac{1}{\sigma_0 - 1} + C.$$
--
--   The constant $C$ is uniform: it does not depend on $\sigma_0$ or on the height $t$. The bound captures the two regimes at once --- near the pole ($\sigma_0 \to 1^+$) the term $(\sigma_0-1)^{-1}$ dominates, matching the simple pole of $-\zeta'/\zeta$ of residue $1$ at $s = 1$, while away from the pole the whole expression is bounded by an absolute constant.
--
--   The estimate follows from the Dirichlet series $-\zeta'/\zeta(s) = \sum_n \Lambda(n) n^{-s}$, absolutely convergent for $\operatorname{Re}(s) > 1$, whose norm is at most $-\zeta'/\zeta(\sigma_0)$ on the vertical line. In the PNT+ contour arguments it serves as the "trivial" a-priori bound on the integrand of the Perron integral for the (smoothed) Chebyshev function on contours lying just to the right of $\operatorname{Re}(s) = 1$, before the finer zero-free-region bounds take over inside the critical strip.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2829-L3009

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

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt

theorem triv_bound_zeta :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C := by sorry
