-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_prop_mumu
-- name    : Zeta23.PrimeSide.prop_mumu
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:23:38.47385+00:00
-- url     : https://prove2.me/theorems/b4cb386a-16c8-4feb-83ba-38dfb958e967
-- title:
--   Diagonal term $\mathcal{M}[\mu,\mu] = 2\pi b L \int_T^{2T} \mu^2 + O(l^2 \log L)$ ([prop:mumu])
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\mathcal{M}[u_1,u_2] := \iint_{I \times I} \Phi(\tau-\tau')^2\, u_1(\tau)\, u_2(\tau')\, d\tau\, d\tau'$ is the symmetric bilinear form of §5.4 (Lean's `Mform`). Here $\mu$ is the archimedean density [eq:mudef], $\mu(\tau) = \tfrac{1}{2\pi}\operatorname{Re}\tfrac{\Gamma'}{\Gamma}\bigl(\tfrac14 + \tfrac{i\tau}{2}\bigr) - \tfrac{\log\pi}{2\pi}$, and $b = L^{-1}\int \varphi^4$ is the taper constant of [eq:abdef].
--
--   **Statement.** Assume H-$\Gamma$ (`Zeta23.GammaFacts`), H-cheb (`Zeta23.ChebyshevMertens`), and $0 < \lambda \le 1$ (the latter two are unused mathematically but kept so the statement matches the fixed interface shared with the other prime-side propositions). Then there is a constant $C$ such that, eventually in the core-quantified sense (The quantifier `EventuallyAtCore` $c_\varrho\ \lambda\ P$ asserts: there is a threshold $T_0$ such that $P(p,F)$ holds for every setting $p$ with bandwidth ratio $\lambda$ and $T \ge T_0$, and every taper datum $F$ satisfying the core local hypotheses (the majorant bound $|\hat{\varphi}|, |\Phi| \le \psi$ with $\psi(r) = \min(L,\, 2/|r|,\, c_\varrho/(w r^2))$ [eq:psidef], the ranges $0 < \lambda$, $1 \le w \le L/8$, and the standard taper facts), where $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].),
--   $$\Bigl|\mathcal{M}[\mu,\mu] - 2\pi\, b\, L \int_T^{2T} \mu(\tau)^2\, d\tau\Bigr| \le C \cdot l^2 \log L.$$
--   This is [prop:mumu] of §5.4.
--
--   **Role.** The $\mu$–$\mu$ diagonal term of the bilinear expansion [eq:Msplit] of $\mathcal{M}[\nu_X,\nu_X]$; it supplies the field `prop_mumu` of the `Facts` record in `Zeta23.PrimeSide.concreteFacts` and is cited by the other prime-side propositions sharing the same interface.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/MuMu.lean#L220-L287, docstring tag [prop:mumu]

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

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable (cϱ lam : ℝ)
set_option linter.unusedVariables false

theorem Zeta23.PrimeSide.prop_mumu (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu Zeta23.mu
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
        ≤ C * (p.l ^ 2 * Real.log p.L)) := by sorry
