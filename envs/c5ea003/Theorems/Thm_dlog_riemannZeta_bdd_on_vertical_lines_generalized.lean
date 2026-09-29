-- Prove2me | Theorems.Thm_dlog_riemannZeta_bdd_on_vertical_lines_generalized
-- name    : dlog_riemannZeta_bdd_on_vertical_lines_generalized
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:38:34.092294+00:00
-- url     : https://prove2.me/theorems/4e38934b-623f-4369-956f-1001acd77ccf
-- title:
--   The logarithmic derivative $-\zeta'/\zeta$ on vertical lines right of $\sigma_0 > 1$ is dominated by its value at $\sigma_0$
-- statement:
--   Let $\sigma_0, \sigma_1, t \in \mathbb{R}$ with $1 < \sigma_0$ and $\sigma_0 \leq \sigma_1$. Then the logarithmic derivative of the Riemann zeta function satisfies
--
--   $$\left\| -\frac{\zeta'(\sigma_1 + it)}{\zeta(\sigma_1 + it)} \right\| \;\leq\; \left\| \frac{\zeta'(\sigma_0)}{\zeta(\sigma_0)} \right\|.$$
--
--   That is, at any point $s = \sigma_1 + it$ with real part at least $\sigma_0 > 1$, the modulus of $-\zeta'/\zeta$ is bounded by the value of $|\zeta'/\zeta|$ at the real point $\sigma_0$, uniformly in the height $t$. This reflects the Dirichlet series representation $-\zeta'/\zeta(s) = \sum_{n \geq 1} \Lambda(n) n^{-s}$ valid for $\operatorname{Re} s > 1$, whose absolute value is maximized on the real axis and is monotone decreasing in the real part.
--
--   In the Prime Number Theorem argument this uniform bound controls the integrand $-\zeta'/\zeta$ along the vertical segments and far-right portions of the contour, where the Dirichlet series converges absolutely and no zero-free-region input is needed.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2781-L2827

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
open scoped ComplexOrder

theorem dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (σ₀ σ₁ t : ℝ) (σ₀_gt_one : 1 < σ₀) (σ₀_lt_σ₁ : σ₀ ≤ σ₁) :
    ‖(- ζ' (σ₁ + t * I) / ζ (σ₁ + t * I))‖ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by sorry
