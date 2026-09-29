-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_prop_cross_muP
-- name    : Zeta23.PrimeSide.prop_cross_muP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:21:59.008972+00:00
-- url     : https://prove2.me/theorems/34f8f286-917c-48b4-81e5-8e2fc28a2c41
-- title:
--   Cross term $\mathcal{M}[\mu, P_X] \ll l\sqrt{X}$ ([prop:cross] (i))
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\mathcal{M}[u_1,u_2] := \iint_{I \times I} \Phi(\tau-\tau')^2\, u_1(\tau)\, u_2(\tau')\, d\tau\, d\tau'$ is the symmetric bilinear form of §5.4 (Lean's `Mform`). Here $\mu$ is the archimedean density [eq:mudef], $\mu(\tau) = \tfrac{1}{2\pi}\operatorname{Re}\tfrac{\Gamma'}{\Gamma}\bigl(\tfrac14 + \tfrac{i\tau}{2}\bigr) - \tfrac{\log \pi}{2\pi}$, and $P_X$ is the prime-power density [eq:Pdef], $P_X(\tau) = -\tfrac1\pi \sum_{n \le X} \Lambda(n) n^{-1/2} \cos(\tau \log n)$.
--
--   **Statement.** Assume H-$\Gamma$ (`Zeta23.GammaFacts`), H-cheb (`Zeta23.ChebyshevMertens`), and $0 < \lambda \le 1$. Then there is a constant $C$ such that, eventually in the core-quantified sense (The quantifier `EventuallyAtCore` $c_\varrho\ \lambda\ P$ asserts: there is a threshold $T_0$ such that $P(p,F)$ holds for every setting $p$ with bandwidth ratio $\lambda$ and $T \ge T_0$, and every taper datum $F$ satisfying the core local hypotheses (the majorant bound $|\hat{\varphi}|, |\Phi| \le \psi$ with $\psi(r) = \min(L,\, 2/|r|,\, c_\varrho/(w r^2))$ [eq:psidef], the ranges $0 < \lambda$, $1 \le w \le L/8$, and the standard taper facts), where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].),
--   $$\bigl|\mathcal{M}[\mu, P_X]\bigr| \le C \cdot l \sqrt{X}.$$
--   This is part (i) of [prop:cross] (§5.4).
--
--   **Role.** Proved in `Zeta23.PrimeSideA.CrossMuP` in exactly the interface form used by `PrimeSideA.lean` (which imports this file); it supplies the field `cross_muP` of the `Facts` record in `Zeta23.PrimeSide.concreteFacts` and is cited by the other prime-side propositions ([eq:Msplit], [prop:trace], [prop:mumu], the remaining cross terms) sharing that interface.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/CrossMuP.lean#L67-L152, docstring tag [prop:cross]

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
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.prop_cross_muP (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu (Zeta23.PX p.X)| ≤ C * (p.l * Real.sqrt p.X)) := by sorry
