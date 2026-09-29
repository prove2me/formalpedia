-- Prove2me | Definitions.Def_ZetaBounds_defs
-- name    : ZetaBounds_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:49:53.454559+00:00
-- url     : https://prove2.me/theorems/31032376-68b0-4d6c-8bf5-1aacf266a5c3
-- title:
--   Euler–Maclaurin representation $\zeta_0(N,s)$ of the Riemann zeta function and its derivative
-- statement:
--   This bundle defines the truncated Euler–Maclaurin representation of the Riemann zeta function used to obtain explicit bounds on $\zeta$ and $\zeta'$ to the left of the line $\Re s = 1$, where the Dirichlet series no longer converges.
--
--   **Main definitions.** Write $\zeta$ for the Riemann zeta function and $\zeta'$ for its derivative.
--
--   - `riemannZeta0 N s` (notation $\zeta_0$) — the finite-plus-integral expression $\zeta_0(N, s) = \sum_{n=0}^{N} \frac{1}{n^s} - \frac{N^{1-s}}{1-s} - \frac{N^{-s}}{2} + s \int_N^\infty \frac{\lfloor x\rfloor + \tfrac{1}{2} - x}{x^{s+1}}\,dx$, obtained by first-order Euler–Maclaurin summation applied to $\sum n^{-s}$. The sawtooth kernel $\lfloor x\rfloor + \tfrac12 - x = -B_1(x)$ makes the integral absolutely convergent for $\Re s > 0$, so $\zeta_0(N, \cdot)$ extends holomorphically past the abscissa of convergence and agrees with $\zeta$ there ($\zeta_0(N,s) = \zeta(s)$ for $\Re s > 0$, $s \ne 1$).
--
--   - `ζ₀' N s` — the term-by-term derivative of the above: $\sum_{n=0}^{N} \frac{-\log n}{n^s} + \Bigl(-\frac{N^{1-s}}{(1-s)^2} + \frac{(\log N)\,N^{1-s}}{1-s}\Bigr) + \frac{(\log N)\,N^{-s}}{2} + \int_N^\infty \frac{\lfloor x\rfloor + \tfrac12 - x}{x^{s+1}}\,dx + s \int_N^\infty \frac{(\lfloor x\rfloor + \tfrac12 - x)(-\log x)}{x^{s+1}}\,dx$, giving matching access to $\zeta'(s)$ in the same region.
--
--   **Downstream use.** Choosing $N \asymp |t|$ in $\zeta_0$ yields the classical growth estimates $|\zeta(\sigma + it)| \ll \log|t|$ and $|\zeta'(\sigma+it)| \ll (\log|t|)^2$ near $\Re s = 1$, which combine with the non-vanishing of $\zeta$ to give the zero-free region and the bound $|\zeta'/\zeta(\sigma+it)| \le C(\log|t|)^9$ (`LogDerivZetaHasBound`) consumed by the contour-integration proof of the prime number theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean (definitions vendored from this file)

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

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics


local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta


-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/


-- Alternative cleaner proof using more direct approach


/- The set should be open so that f'(p) = O(1) for all p ∈ U -/


noncomputable def riemannZeta0 (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
  (- N ^ (1 - s)) / (1 - s) + (- N ^ (-s)) / 2
      + s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0


-- move near `Real.differentiableAt_rpow_const_of_ne`


noncomputable def ζ₀' (N : ℕ) (s : ℂ) : ℂ :=
    ∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * Real.log n +
    (-N ^ (1 - s) / (1 - s) ^ 2 + Real.log N * N ^ (1 - s) / (1 - s)) +
    Real.log N * N ^ (-s) / 2 +
    (1 * (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1)) +
    s * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x))


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
--TODO generalize to any LSeries with nonnegative coefficients


