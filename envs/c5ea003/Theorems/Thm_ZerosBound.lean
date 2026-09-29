-- Prove2me | Theorems.Thm_ZerosBound
-- name    : ZerosBound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:24.499864+00:00
-- url     : https://prove2.me/theorems/c3517640-7df9-4cb9-aa6a-4f657187895a
-- title:
--   Jensen-type bound: the number of zeros in $\overline{D}(0,r)$ is at most $\frac{\log B}{\log(R/r)}$
-- statement:
--   Let $0 < r < 1$, $r < R < 1$, and let $f : \mathbb{C} \to \mathbb{C}$ be analytic on a neighbourhood of the closed unit disk with $f(0) = 1$. Assume the zero set of $f$ in the closed unit disk, $\{\rho : \|\rho\| \le 1,\ f(\rho) = 0\}$, is finite, and that $\|f(z)\| \le B$ for all $\|z\| \le R$.
--
--   **Statement.** The zeros of $f$ in the closed disk $\overline{D}(0,r)$, counted with multiplicity, satisfy
--   $$\sum_{\substack{\rho\,:\, \|\rho\| \le r \\ f(\rho) = 0}} m_\rho \;\le\; \frac{1}{\log(R/r)}\, \log B,$$
--   where $m_\rho$ is the order of vanishing of $f$ at $\rho$ (Mathlib's `analyticOrderNatAt`), and the sum is over the (finite) set of zeros of $f$ of norm at most $r$.
--
--   This is the classical Jensen-formula-style zero-counting bound: a growth bound $B$ on the slightly larger disk of radius $R$ controls the number of zeros in the disk of radius $r$. In the module `Zeta23.FromPNTPlus.StrongPNTPrefix` it is a workhorse for the zero-counting side of the project: it feeds `Zeta23.RvM.half_count_large` and `Zeta23.RvM.reZeroSet_card_le_of_growth` in the Riemann–von Mangoldt counting arguments, and `Zeta23.WeilEF.logDeriv_partial_fraction_disk` and `Zeta23.WeilEF.norm_logDeriv_Cf_le` in the partial-fraction analysis of $\zeta'/\zeta$ for the Weil explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean#L453-L481

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory
open Classical

theorem ZerosBound {B r R : ℝ} {f : ℂ → ℂ}
    (r_pos : 0 < r) (r_lt_one : r < 1) (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0_eq_one : f 0 = 1)
    (finiteZeros : (SetOfZeros 1 f).Finite) (fz_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∑ ρ ∈ (finiteSetOfZeros_mono r_lt_one finiteZeros).toFinset, analyticOrderNatAt f ρ ≤
      1 / Real.log (R / r) * Real.log B := by sorry
