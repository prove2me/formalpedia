-- Prove2me | Definitions.Def_Zeta23_RvM_LocalCount
-- name    : Zeta23_RvM_LocalCount
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:23:12.983349+00:00
-- url     : https://prove2.me/theorems/5504fce8-a5c5-42d3-9c9a-75eef48f76c8
-- title:
--   Setup for the local zero count $N(t,t+1] \le A_0\log(|t|+3)$
-- statement:
--   Definitions for the local (unit-window) zero count of $\zeta$, the `local_count` field of `Zeta23.RiemannVonMangoldt` ([Tit86, Thm 9.2]).
--
--   **Members.**
--   - `gfun s₀ c u z` — the rescaled function $g(z):=\zeta(s_0+cz)\cdot u$, used to transport a Jensen-type disc zero-count bound (the ported PNT+ `ZerosBound`) to a window of the critical strip: with $s_0 = 2+(t+\tfrac12)i$ and a suitable scale $c$, the zeros with $\beta\ge\tfrac12$ and ordinate in $(t,t+1]$ land in a small disc while the large disc avoids the pole and stays in a region where the growth bound on $\zeta$ applies.
--   - `NhalfR t` — the number of zeros with real part $\beta\ge \tfrac12$ and ordinate in the window $(t,t+1]$, counted with multiplicity, as a real number:
--   $$N_{1/2}(t) := \sum_{\substack{\rho\,:\, t<\gamma\le t+1\\ \beta\ge 1/2}} m_\rho .$$
--
--   **Role.** The module proves $N(t,t+1]\le A_0\log(|t|+3)$ for all real $t$ (two-sided form) for `zetaZeroConfig`: one counts only the zeros with $\beta\ge\tfrac12$ and doubles (via the $\rho\mapsto1-\bar\rho$ symmetry, `Halving.lean`), then bounds `NhalfR` by the Jensen-type disc count applied to `gfun`, never evaluating $\zeta$ left of $\sigma\approx0.19$ so that no Stirling estimates are needed. The local count feeds the tail bound [prop:tail] and the zero-sum summability of the explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/LocalCount.lean

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/LocalCount.lean

H-RvM's local count for Mathlib's ζ:  N(t, t+1] ≤ A₀ log(|t| + 3) for all real t
(= Zeta23.RiemannVonMangoldt.local_count at Z := zetaZeroConfig; [Tit86, Thm 9.2]).

Route (never evaluating ζ left of σ = 0.19, so no Stirling is needed):
 * count only zeros with β ≥ 1/2 and double (Zeta23.ZeroConfig.N_le_two_mul_half, Zeta23/RvM/Halving.lean,
   via the ρ ↦ 1−ρ̄ symmetry);
 * Jensen-type zero count on a disc: the ported PNT+ `ZerosBound` (Zeta23/FromPNTPlus/StrongPNTPrefix.lean,
   Apache-2.0) applied to g(w) := ζ(c₀ + 1.9 w)/ζ(c₀), c₀ := 2 + (t+½)i, r = 0.84, R = 0.95:
   the β ≥ 1/2 part of the window lies in ‖w‖ ≤ 0.84 (1.5² + 0.5² ≤ (1.9·0.84)²), the big disc stays in
   σ ≥ 0.195 and at distance ≥ 1 from the pole for |t| ≥ 4;
 * ζ-growth ‖ζ(s)‖ ≤ C(|Im s|+3)^A on σ ≥ 0.15, ‖s−1‖ ≥ 1 and ‖ζ(2+it)‖ ≥ 1/3
   (Zeta23.RvM.zeta_growth_right / zeta_lower_bound_two, Zeta23/RvM/ZetaGrowth.lean);
 * |t| < 4 by the finite constant N(−4, 5].
-/


open Complex Set Filter Topology Metric

noncomputable section

namespace Zeta23.RvM


/-- the rescaled function g(z) := ζ(s₀ + c z) · u. -/
def gfun (s₀ c u : ℂ) (z : ℂ) : ℂ := riemannZeta (s₀ + c * z) * u







/-- zeros with β ≥ 1/2 in the window (t, t+1], with multiplicity, as a real number. -/
def NhalfR (t : ℝ) : ℝ := ∑ᶠ ρ ∈ zetaZeroConfig.window t (t + 1) ∩ {ρ | 1/2 ≤ ρ.re}, (zeroMult ρ : ℝ)





end Zeta23.RvM


