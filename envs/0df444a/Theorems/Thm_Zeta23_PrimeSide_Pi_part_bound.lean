-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_Pi_part_bound
-- name    : Zeta23.PrimeSide.Pi_part_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:06:51.732196+00:00
-- url     : https://prove2.me/theorems/7a7bbad6-3338-4614-b486-f41a0c46e48f
-- title:
--   $\Pi$-part of a diagonal entry: $|G^\Pi| \le \frac{6\sqrt X}{t}\,2\pi a L + \frac{12\sqrt X}{t^2}\int\hat\varphi^2 r^2$
-- statement:
--   Let $p$ be a parameter setting with prime cutoff $X$ and window length $L$, and $F$ a taper datum satisfying `LocalHypsCore`; $a = L^{-1}\int\varphi^2$ is its mass parameter, so that $\int\hat\varphi(r)^2\,dr = 2\pi a L$ (Plancherel). $\Pi_X$ is the pole-term density [eq:Pidef].
--
--   Then for every $t \ge 2$,
--   $$\Bigl|\int_{\mathbb R}\hat\varphi(r)^2\,\Pi_X(t+r)\,dr\Bigr| \;\le\; \frac{6\sqrt X}{t}\cdot 2\pi a L \;+\; \frac{12\sqrt X}{t^2}\int_{\mathbb R}\hat\varphi(r)^2 r^2\,dr,$$
--   by integrating the shifted bound `PiX_shift_bound` against $\hat\varphi^2$. This is §5.2's "$|G^\Pi_{kk}| \le 6\sqrt X\cdot 2\pi a L/T + O(\sqrt X\,T^{-3})$" (the second moment $\int\hat\varphi^2 r^2$ is $O(1)$ by the package).
--
--   Applied at $t = \tau_k$, it controls the $\Pi$-part of each diagonal Gram entry in `prop_trace_mu`, the trace asymptotics [prop:trace].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1202-L1224, docstring tag [prop:trace]

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

theorem Zeta23.PrimeSide.Pi_part_bound (hF : LocalHypsCore cϱ p F) {t : ℝ} (ht : 2 ≤ t) :
    |∫ r, F.phiHat r ^ 2 * Zeta23.PiX p.X (t + r)|
      ≤ (6 * Real.sqrt p.X / t) * (2 * π * F.a * p.L)
        + (12 * Real.sqrt p.X / t ^ 2) * ∫ r, F.phiHat r ^ 2 * r ^ 2 := by sorry
