-- Prove2me | Theorems.Thm_Zeta23_ZetaBnd_aux1b
-- name    : Zeta23_ZetaBnd_aux1b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:25.259992+00:00
-- url     : https://prove2.me/theorems/4aabc7b1-6d08-4303-ba37-fab8db96e972
-- title:
--   Euler–Maclaurin remainder bound: $\big\|\int_N^\infty \frac{\lfloor x\rfloor + 1/2 - x}{x^{s+1}}\, dx\big\| \le N^{-\sigma}/\sigma$
-- statement:
--   Let $N \ge 1$ be a natural number and $s = \sigma + it$ with $\sigma > 0$. The integrand $\frac{\lfloor x \rfloor + 1/2 - x}{x^{s+1}}$ is the sawtooth-type remainder appearing in the Euler–Maclaurin (Riemann–Siegel-style) integral representation of $\zeta$ on the right half-plane, with $x^{s+1}$ the complex power of the real variable $x$. The assertion is the tail bound
--   $$\Big\| \int_N^{\infty} \frac{\lfloor x \rfloor + 1/2 - x}{x^{\,\sigma + it + 1}}\, dx \Big\| \;\le\; \frac{N^{-\sigma}}{\sigma},$$
--   obtained by bounding the numerator by $1/2$ in absolute value and integrating $x^{-\sigma-1}$ (formally, via a limit of truncated interval integrals).
--
--   This lemma lives in `Zeta23.FromPNTPlus.ZetaBounds`, ported from the PrimeNumberTheoremAnd project. In this repository it feeds the growth estimate `Zeta23.RvM.norm_riemannZeta_le_of_re_pos` — a bound on $|\zeta|$ in the critical strip used by the Riemann–von Mangoldt zero-counting development (argument principle + Backlund), which in turn discharges the H-RvM hypothesis of Theorem A unconditionally.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ZetaBounds.lean#L814-L838

import Batteries.Tactic.Lemma
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds

set_option lang.lemmaCmd true
open Complex Topology Filter Interval Set Asymptotics
local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0
open MeasureTheory

theorem Zeta23_ZetaBnd_aux1b (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (σpos : 0 < σ) :
    ‖∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ N ^ (-σ) / σ := by sorry
