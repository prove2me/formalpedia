-- Prove2me | Theorems.Thm_Zeta23_Zeta0EqZeta
-- name    : Zeta23_Zeta0EqZeta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:13.40711+00:00
-- url     : https://prove2.me/theorems/d944f426-5b80-4855-842a-cc6d8e430bc0
-- title:
--   The Euler–Maclaurin representation $\zeta_0(N,s)$ equals $\zeta(s)$ for $\operatorname{Re} s > 0$
-- statement:
--   For a natural number $N$ and $s \in \mathbb{C}$, define the alternative zeta function $\zeta_0(N, s)$ (`riemannZeta0`) by the Euler–Maclaurin-type expression
--   $$\zeta_0(N, s) \;=\; \sum_{n=0}^{N} \frac{1}{n^s} \;-\; \frac{N^{1-s}}{1-s} \;-\; \frac{N^{-s}}{2} \;+\; s \int_N^\infty \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}}\, dx,$$
--   where the $n = 0$ term of the sum is $0$ (Lean's convention $0^s = 0$ for $s \ne 0$), so the sum is effectively over $1 \le n \le N$.
--
--   **Statement.** For every $N \ge 1$ and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$ and $s \ne 1$,
--   $$\zeta_0(N, s) = \zeta(s),$$
--   where $\zeta$ is Mathlib's `riemannZeta`. That is, the finite-sum-plus-integral representation analytically continues the Dirichlet series and agrees with the Riemann zeta function throughout the right half-plane $\operatorname{Re} s > 0$ away from the pole at $s = 1$.
--
--   This identity, in the module `Zeta23.FromPNTPlus.ZetaBounds` (ported from the PrimeNumberTheoremAnd project), lets growth estimates for $\zeta$ be read off from the explicit representation: it is consumed by `Zeta23.RvM.norm_riemannZeta_le_of_re_pos`, the polynomial bound on $|\zeta(s)|$ used in the Riemann–von Mangoldt zero-counting part of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/ZetaBounds.lean#L1150-L1178

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

theorem Zeta23_Zeta0EqZeta {N : ℕ} (N_pos : 0 < N) {s : ℂ} (reS_pos : 0 < s.re) (s_ne_one : s ≠ 1) :
    ζ₀ N s = riemannZeta s := by sorry
