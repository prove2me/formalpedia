-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sum_a2g_lowerPrime
-- name    : Zeta23.PrimeSide.sum_a2g_lowerPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:27:40.273853+00:00
-- url     : https://prove2.me/theorems/3f39878d-09ff-41f8-be5d-faf47afa3e4e
-- title:
--   Sandwich lower bound: $\sum_{n \le X} \Lambda(n)^2 n^{-1} g(\log n) \ge (L - 2w)^3/6 - O(L^2)$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef]. The main-term sum of [prop:PP] is
--   $$\Sigma(X, g) := \sum_{0 < n \le \lfloor X \rfloor} \frac{\Lambda(n)^2}{n}\, g(\log n)$$
--   (Lean's `sumA2g`; note $a_n^2 = \Lambda(n)^2/n$), where $g = \varphi^2 \star \varphi^2$ is the autocorrelation from the taper datum $F$.
--
--   **Statement.** Assume H-cheb (`Zeta23.ChebyshevMertens`) and $0 < \lambda \le 1$. Then there is a constant $C$ such that, eventually in the sense of `EventuallyAt` (for all settings $p$ with ratio $\lambda$ and $T \ge T_0$, and all taper data $F$ satisfying the **full** local hypotheses `LocalHyps` — this direction uses the lower bound on $g$, hence the full package rather than the core one),
--   $$\frac{(L - 2w)^3}{6} - C\, L^2 \;\le\; \Sigma(X, g).$$
--   The proof restricts the sum to $n \le X e^{-2w}$, where [eq:gbounds] gives $g(\log n) \ge L - 2w - \log n$, and applies the Mertens-type estimate [eq:cheb2].
--
--   **Role.** The lower half of the sandwich for the [prop:PP] main term; it supplies the field `sum_lower` of the `Facts` record via `Zeta23.PrimeSide.concreteFacts`, entering the second-moment asymptotic [eq:tr2] and hence the ratio [eq:ratio].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L118-L162

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
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ lam : ℝ}
variable {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.sum_a2g_lowerPrime (hcheb : Zeta23.ChebyshevMertens) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      (p.L - 2 * p.w) ^ 3 / 6 - C * p.L ^ 2 ≤ sumA2g p.X F.g) := by sorry
