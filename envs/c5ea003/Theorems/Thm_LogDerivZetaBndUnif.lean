-- Prove2me | Theorems.Thm_LogDerivZetaBndUnif
-- name    : LogDerivZetaBndUnif
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:57:26.141047+00:00
-- url     : https://prove2.me/theorems/068fc6bc-6626-43a8-a271-5a116516808c
-- title:
--   Uniform bound $|\zeta'/\zeta(\sigma+it)| \le C(\log|t|)^9$ in a zero-free region of width $A/(\log|t|)^9$
-- statement:
--   There exist constants $A\in(0,\tfrac12]$ and $C>0$ such that for every $\sigma\in\mathbb{R}$ and $t\in\mathbb{R}$ with $|t|>3$ and
--
--   $$\sigma \ \ge\ 1-\frac{A}{(\log|t|)^{9}},$$
--
--   the logarithmic derivative of the Riemann zeta function satisfies
--
--   $$\left\| \frac{\zeta'}{\zeta}(\sigma+it) \right\| \ \le\ C\,(\log|t|)^{9}.$$
--
--   This is the standard quantitative estimate accompanying the classical (de la Vallée-Poussin-type) zero-free region, here in the polynomial-in-$\log$ form with exponent $9$ used throughout this development: inside a region extending distance $A/(\log|t|)^9$ to the left of the line $\operatorname{Re} s=1$, the function $\zeta'/\zeta$ grows at most like $(\log|t|)^9$, uniformly in $\sigma$ and $t$.
--
--   It is the key input for bounding the integrand along the pulled contour in the proof of the Prime Number Theorem with error term: the width of the zero-free region and the polynomial growth bound together determine the exponent $1/10$ in the final error term $O\bigl(x\exp(-c(\log x)^{1/10})\bigr)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L3011-L3079

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

theorem LogDerivZetaBndUnif :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
      C * Real.log |t| ^ 9 := by sorry
