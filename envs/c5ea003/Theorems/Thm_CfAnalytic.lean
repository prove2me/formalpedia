-- Prove2me | Theorems.Thm_CfAnalytic
-- name    : CfAnalytic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:25:49.006954+00:00
-- url     : https://prove2.me/theorems/6fb69b90-3411-4c3a-8731-c34df1f211a3
-- title:
--   Analyticity of the zero-removed factor $C_f$ on a smaller disk
-- statement:
--   For $r \in \mathbb{R}$ and $f : \mathbb{C} \to \mathbb{C}$, the project defines the *zero-removed factor* $C_f(r, f)$ as follows: if the zero set $\{\rho : \|\rho\| \le r,\ f(\rho) = 0\}$ is finite, then away from the zeros
--   $$C_f(z) = \frac{f(z)}{\prod_{\rho} (z - \rho)^{m_\rho}},$$
--   where the product runs over the zeros $\rho$ of $f$ in the closed disk of radius $r$ and $m_\rho$ is the order of vanishing of $f$ at $\rho$ (Mathlib's `analyticOrderNatAt`); at a zero $z$ itself the numerator $f(z)$ is replaced by the local unit `ZeroFactor f z` and the factor $(z - z)^{m_z}$ is omitted from the product. (If the zero set is infinite, $C_f$ is defined to be the constant $1$.)
--
--   **Statement.** Suppose $r < R < 1$, $f$ is analytic on a neighbourhood of the closed unit disk $\overline{D}(0,1)$, and $f(0) \ne 0$. Then $C_f(r, f)$ is analytic on a neighbourhood of the closed disk $\overline{D}(0,R)$.
--
--   In other words, dividing out the zeros of $f$ inside radius $r$ produces a genuinely analytic (and, by construction, zero-free on the smaller disk) function. This lemma, from the module `Zeta23.FromPNTPlus.StrongPNTPrefix`, underpins the Landau-style lemmas of the Weil explicit-formula development: it is consumed by the zero-counting bound `ZerosBound` and by `Zeta23.WeilEF.logDeriv_split` and `Zeta23.WeilEF.norm_logDeriv_Cf_le`, which split $f'/f$ into a sum over zeros plus the analytic term $C_f'/C_f$ and bound the latter.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/FromPNTPlus/StrongPNTPrefix.lean#L261-L310

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

theorem CfAnalytic {r R : ℝ} {f : ℂ → ℂ}
    (r_lt_R : r < R) (R_lt_one : R < 1)
    (hfAnalytic : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf_neq_zero_at_zero : f 0 ≠ 0) :
    AnalyticOnNhd ℂ (Cf r f) (Metric.closedBall (0 : ℂ) R) := by sorry
