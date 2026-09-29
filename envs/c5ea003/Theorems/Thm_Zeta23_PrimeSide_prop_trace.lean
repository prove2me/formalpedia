-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_prop_trace
-- name    : Zeta23.PrimeSide.prop_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:26:58.906067+00:00
-- url     : https://prove2.me/theorems/0bccde90-0439-41c0-bc84-b5f1b28c3c17
-- title:
--   Trace asymptotic $\operatorname{tr}\tilde{G} = aL \cdot N(T,2T) + O(L\sqrt{X})$ ([prop:trace])
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef]. The prime-side matrix entries are $G_{kk} = \int_{\mathbb{R}} \hat{\varphi}(\tau - \tau_k)^2\, \nu_X(\tau)\, d\tau$ with $\nu_X = \mu + \Pi_X + P_X$ [eq:nudef], and $\operatorname{tr}\tilde{G} = L^{-1}\sum_{k < d} G_{kk}$ (Lean's `trGtA`); $\ell_1 = l + 2\log 2 - 1$.
--
--   **Statement.** Assume H-$\Gamma$ (`Zeta23.GammaFacts`), H-cheb (`Zeta23.ChebyshevMertens`), $0 < \lambda \le 1$, and fix a real constant $A$. Then there is a constant $C$ such that, eventually in the core-quantified sense (The quantifier `EventuallyAtCore` $c_\varrho\ \lambda\ P$ asserts: there is a threshold $T_0$ such that $P(p,F)$ holds for every setting $p$ with bandwidth ratio $\lambda$ and $T \ge T_0$, and every taper datum $F$ satisfying the core local hypotheses (the majorant bound $|\hat{\varphi}|, |\Phi| \le \psi$ with $\psi(r) = \min(L,\, 2/|r|,\, c_\varrho/(w r^2))$ [eq:psidef], the ranges $0 < \lambda$, $1 \le w \le L/8$, and the standard taper facts), where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].), the following holds: for **every** real number $N$ satisfying the Riemann–von Mangoldt-type bound $|N - T\ell_1/2\pi| \le A\, l$ [eq:RvM],
--   $$\bigl|\operatorname{tr}\tilde{G} - a\, L\, N\bigr| \le C \cdot L\sqrt{X}.$$
--   Here $N$ is an abstract real standing in for the zero count $N(T,2T)$ — the prime side is $\zeta$-free, and $N(T,2T)$ enters only through the hypothesis $|N - T\ell_1/2\pi| \le A l$; the two analytic inputs are exactly what the paper's proof of [prop:trace] (§5.2) uses, namely [eq:muints] (field `int_mu` of `GammaFacts`) and [eq:RvM].
--
--   **Role.** The first-moment half of the trace computation; it supplies the field `prop_trace` of the `Facts` record in `Zeta23.PrimeSide.concreteFacts`, feeding the ratio $\bigl(\operatorname{tr}\tilde{G}\bigr)^2/\operatorname{tr}\tilde{G}^2$ in the [thm:traces] assembly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA.lean#L296-L366, docstring tag [prop:trace]

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.prop_trace (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F => ∀ N : ℝ,
      |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtA p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X)) := by sorry
