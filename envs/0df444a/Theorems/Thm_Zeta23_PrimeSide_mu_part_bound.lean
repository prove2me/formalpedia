-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_mu_part_bound
-- name    : Zeta23.PrimeSide.mu_part_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:25:42.964766+00:00
-- url     : https://prove2.me/theorems/0fa949c2-482b-4f7b-903a-36c6c4797900
-- title:
--   $\mu$-part of [prop:trace] at one grid point: $\int\hat\varphi^2\mu(t+\cdot) = 2\pi a L\,\mu(t) + O(\log L/t)$
-- statement:
--   Work in the abstract prime-side setting: taper data $F$ with core hypotheses `LocalHypsCore` (in particular $\int\hat\varphi(r)^2dr=2\pi aL$), and let $\mu$ be the archimedean density [eq:mudef]. Assume H-$\Gamma$ (`Zeta23.GammaFacts`) and suppose $K$ is a constant for which the increment bound holds: $|\mu(t+r)-\mu(t)|\le(K|r|+10r^2)/t$ for all $t\ge 2$ and all $r$ (supplied by `mu_increment_bound`).
--
--   Then for every $t\ge 2$:
--   $$\Bigl|\int_{\mathbb{R}}\hat\varphi(r)^2\,\mu(t+r)\,dr\ -\ 2\pi a L\,\mu(t)\Bigr|\ \le\ \frac{K\int\hat\varphi(r)^2|r|\,dr\ +\ 10\int\hat\varphi(r)^2 r^2\,dr}{t}.$$
--   Since $\int\hat\varphi^2|r|\ll\log L$ and $\int\hat\varphi^2r^2=O(1)$ [eq:psiints], this is the paper's "$G^{\mu}_{kk}=2\pi aL\,\mu(\tau_k)+O(\log L/T)$" (§5.2) at a single grid point $t=\tau_k$.
--
--   In module `Zeta23.PrimeSideA.Basic` it is consumed by `prop_trace_mu`: summing over the $d$ grid points gives the $\mu$-contribution to the trace $\operatorname{tr}\widetilde{G}$ in [prop:trace].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1157-L1200, docstring tag [prop:trace]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.mu_part_bound (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) {K : ℝ}
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∫ r, F.phiHat r ^ 2 * Zeta23.mu (t + r)) - 2 * π * F.a * p.L * Zeta23.mu t|
      ≤ (K * (∫ r, F.phiHat r ^ 2 * |r|) + 10 * (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by sorry
