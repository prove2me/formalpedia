-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sum_P_part_bound
-- name    : Zeta23.PrimeSide.sum_P_part_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:26:28.488+00:00
-- url     : https://prove2.me/theorems/f0af8f26-24d0-44ee-a3e9-4d3bfd9f0704
-- title:
--   Sum of the $P$-parts of the diagonal: $\bigl|\sum_{k<d} G^P_{kk}\bigr| \le (L^2/\log 2) \sum_{n \le X} a_n$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef]. The $P$-part of the $k$-th diagonal matrix entry is $G^P_{kk} = \int_{\mathbb{R}} \hat{\varphi}(r)^2\, P_X(\tau_k + r)\, dr$, where $P_X$ is the prime-power density [eq:Pdef]; $a_n := \Lambda(n)/\sqrt{n}$, and the sum $\sum_{n \le X}$ runs over $0 < n \le \lfloor X \rfloor$ ($\Lambda$ vanishes off prime powers).
--
--   **Statement.** Assume the core local hypotheses `LocalHypsCore`. Then
--   $$\left| \sum_{k < d} \int_{\mathbb{R}} \hat{\varphi}(r)^2\, P_X(\tau_k + r)\, dr \right| \;\le\; \frac{L^2}{\log 2} \sum_{n \le X} \frac{\Lambda(n)}{\sqrt{n}}.$$
--   This is the §5.2 estimate for the prime-power contribution to the trace: summing the grid over $k < d$ produces, for each frequency $\log n$, a geometric-type factor bounded by $L^2/\log 2$.
--
--   **Role.** Shows the $P_X$-part of $\operatorname{tr}\tilde{G}$ is $O(L\sqrt{X})$ after H-cheb bounds $\sum_{n \le X} \Lambda(n)/\sqrt{n} \le 3\sqrt{X}$; consumed by `Zeta23.PrimeSide.prop_trace_mu`, the $\mu$-form of [prop:trace].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1317-L1353

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

theorem Zeta23.PrimeSide.sum_P_part_bound (hF : LocalHypsCore cϱ p F) :
    |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2 * ∑ n ∈ primeRange p.X, acoef n := by sorry
