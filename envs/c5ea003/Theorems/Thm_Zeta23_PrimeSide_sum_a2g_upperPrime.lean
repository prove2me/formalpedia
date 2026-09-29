-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sum_a2g_upperPrime
-- name    : Zeta23.PrimeSide.sum_a2g_upperPrime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:28:50.071844+00:00
-- url     : https://prove2.me/theorems/abdaab0e-fef9-46dd-89af-e7769aac5aa2
-- title:
--   Sandwich upper bound: $\sum_{n \le X} \Lambda(n)^2 n^{-1} g(\log n) \le L^3/6 + O(L^2)$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef]. The main-term sum of [prop:PP] is
--   $$\Sigma(X, g) := \sum_{0 < n \le \lfloor X \rfloor} \frac{\Lambda(n)^2}{n}\, g(\log n)$$
--   (Lean's `sumA2g`; note $a_n^2 = \Lambda(n)^2/n$), where $g = \varphi^2 \star \varphi^2$ from the taper datum $F$.
--
--   **Statement.** Assume H-cheb (`Zeta23.ChebyshevMertens`) and $0 < \lambda \le 1$. Then there is a constant $C$ such that, eventually in the core-quantified sense (The quantifier `EventuallyAtCore` $c_\varrho\ \lambda\ P$ asserts: there is a threshold $T_0$ such that $P(p,F)$ holds for every setting $p$ with bandwidth ratio $\lambda$ and $T \ge T_0$, and every taper datum $F$ satisfying the core local hypotheses (the majorant bound $|\hat{\varphi}|, |\Phi| \le \psi$ with $\psi(r) = \min(L,\, 2/|r|,\, c_\varrho/(w r^2))$ [eq:psidef], the ranges $0 < \lambda$, $1 \le w \le L/8$, and the standard taper facts), where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].),
--   $$\Sigma(X, g) \;\le\; \frac{L^3}{6} + C\, L^2.$$
--   The proof uses $g \le A_\varphi \le \max(L - |y|, 0)$ pointwise, so $g(\log n) \le L - \log n = \log X - \log n$ for $n \le X$, and then the Mertens-type estimate [eq:cheb2]: $\sum_{n \le x} \frac{\Lambda(n)^2}{n}(\log x - \log n) = \frac{(\log x)^3}{6} + O((\log x)^2)$.
--
--   **Role.** The upper half of the sandwich for the [prop:PP] main term; it supplies the field `sum_upper` of the `Facts` record via `Zeta23.PrimeSide.concreteFacts`, entering the second-moment asymptotic [eq:tr2] and hence the ratio [eq:ratio].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L94-L116

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

theorem Zeta23.PrimeSide.sum_a2g_upperPrime (hcheb : Zeta23.ChebyshevMertens) (_hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      sumA2g p.X F.g ≤ p.L ^ 3 / 6 + C * p.L ^ 2) := by sorry
