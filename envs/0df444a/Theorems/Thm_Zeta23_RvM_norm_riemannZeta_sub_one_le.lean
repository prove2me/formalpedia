-- Prove2me | Theorems.Thm_Zeta23_RvM_norm_riemannZeta_sub_one_le
-- name    : Zeta23.RvM.norm_riemannZeta_sub_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:40:16.342769+00:00
-- url     : https://prove2.me/theorems/829800f7-bac0-426b-a752-25869fe70e9b
-- title:
--   $\|\zeta(s) - 1\| \le \pi^2/6 - 1$ for $\mathrm{Re}\,s \ge 2$
-- statement:
--   **Statement.** For every complex $s$ with $\mathrm{Re}\, s \ge 2$,
--
--   $$\|\zeta(s) - 1\| \;\le\; \sum_{n \ge 2} \frac{1}{n^2} \;=\; \frac{\pi^2}{6} - 1 \;\approx\; 0.6449.$$
--
--   Indeed on this half-plane the Dirichlet series converges absolutely and $\|\zeta(s) - 1\| = \bigl\|\sum_{n \ge 2} n^{-s}\bigr\| \le \sum_{n \ge 2} n^{-2} = \zeta(2) - 1$. Since $\pi^2/6 - 1 < 1$, the bound keeps $\zeta(s)$ in the open right half-plane and bounded away from $0$, uniformly on $\mathrm{Re}\,s \ge 2$.
--
--   **Role.** A workhorse estimate of `Zeta23.RvM.ZetaGrowth`, used wherever $\zeta$ must be controlled on or beyond the line $\mathrm{Re}\,s = 2$: the lower bound at disc centers in the Jensen arguments (`Zeta23.RvM.half_count_large`, `Zeta23.RvM.reZeroSet_card_le_of_growth`), the differentiability of $\log \zeta(2+it)$ and the $O(1)$ vertical bound (`Zeta23.RvM.hasDerivAt_log_riemannZeta_two`, `Zeta23.RvM.vertical_two`), and the partial-fraction expansion `Zeta23.WeilEF.zeta_logDeriv_partial_fraction` on the explicit-formula side.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/ZetaGrowth.lean#L150-L190

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

theorem Zeta23.RvM.norm_riemannZeta_sub_one_le {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ Real.pi ^ 2 / 6 - 1 := by sorry
