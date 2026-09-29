-- Prove2me | Theorems.Thm_Zeta23_RvM_norm_riemannZeta_le_of_re_pos
-- name    : Zeta23.RvM.norm_riemannZeta_le_of_re_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:16.783742+00:00
-- url     : https://prove2.me/theorems/f49f0c25-9fc8-49f9-b17c-64f059e1981d
-- title:
--   Explicit half-plane bound: $\|\zeta(s)\| \le \frac12 + \frac{1}{\|1-s\|} + \frac{\|s\|}{\mathrm{Re}\,s}$
-- statement:
--   **Statement.** For every complex $s$ with $\mathrm{Re}\, s > 0$ and $s \ne 1$,
--
--   $$\|\zeta(s)\| \;\le\; \frac{1}{2} \;+\; \frac{1}{\|1 - s\|} \;+\; \frac{\|s\|}{\mathrm{Re}\, s},$$
--
--   a fully explicit bound valid on the entire right half-plane. It follows from the Euler–Maclaurin representation (the PNT+ port `Zeta0EqZeta` with $N = 1$)
--
--   $$\zeta(s) = \frac{1}{2} - \frac{1}{1 - s} + s \int_1^{\infty} \bigl(\lfloor x\rfloor + \tfrac12 - x\bigr)\, x^{-s-1}\, dx,$$
--
--   where the integral is bounded in norm by $1/\mathrm{Re}\,s$ (via `ZetaBnd_aux1b`).
--
--   **Role.** The starting point of the polynomial growth estimates for $\zeta$ in `Zeta23.RvM.ZetaGrowth`: it feeds `Zeta23.RvM.riemannZeta_linear_growth` and `Zeta23.RvM.zeta_growth_right_at`, which supply the growth hypothesis $\|\zeta(s)\| \le C(|\mathrm{Im}\,s| + 3)^A$ needed by the Jensen-type count `reZeroSet_card_le_of_growth` in the Riemann–von Mangoldt argument.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ZetaGrowth.lean#L52-L72

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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic

open Complex Set MeasureTheory Real

theorem Zeta23.RvM.norm_riemannZeta_le_of_re_pos {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖1 - s‖ + ‖s‖ / s.re := by sorry
