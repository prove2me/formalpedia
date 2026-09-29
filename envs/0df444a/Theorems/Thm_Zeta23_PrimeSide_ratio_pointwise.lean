-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_ratio_pointwise
-- name    : Zeta23.PrimeSide.ratio_pointwise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:37:10.563655+00:00
-- url     : https://prove2.me/theorems/5f4ff2cf-f052-4a84-acfc-045743f86e06
-- title:
--   Pointwise inequality behind [eq:ratio]: $|G^2/G_2 - F(L/\ell)N| \le 2(2\pi A + 5C_1 + C_2)\, E\, F(L/\ell) N$
-- statement:
--   **Setup.** Every quantity is a plain real variable: $T, L, \ell, l_T, E, N, G, G_2, A, C_1, C_2 \in \mathbb{R}$, and $F(x) = x/(1+x^2/3)$ [eq:Fdef]. In the application $G$ plays $\operatorname{tr}\tilde{G}$, $G_2$ plays $\operatorname{tr}\tilde{G}^2$, $N$ the zero count, $\ell$ the scale $\ell_1$, $l_T$ the scale $l$, and $E$ the error scale $\mathcal{E}_T$.
--
--   **Statement.** Assume $T \ge 1$, $L > 0$, $\ell \ge 1$, $l_T \le \ell$, $N > 0$, $E \ge 0$, $1/T \le E$, $A, C_1, C_2 \ge 0$, the smallness conditions $C_1 E \le 1/2$, $C_2 E \le 1/2$, $2\pi A \le T$, and the three input estimates
--   $$|G - L N| \le C_1\, E\, (L N), \qquad \Bigl|G_2 - \tfrac{T L}{2\pi}\bigl(\ell^2 + \tfrac{L^2}{3}\bigr)\Bigr| \le C_2\, E\, \tfrac{T L}{2\pi}\bigl(\ell^2 + \tfrac{L^2}{3}\bigr), \qquad \Bigl|N - \tfrac{T\ell}{2\pi}\Bigr| \le A\, l_T.$$
--   Then
--   $$\Bigl|\frac{G^2}{G_2} - F(L/\ell)\, N\Bigr| \le 2\,(2\pi A + 5 C_1 + C_2)\cdot E \cdot F(L/\ell)\, N.$$
--   The main term $\Phi_0 := F(L/\ell) N$ arises from the identity $F(\lambda_1)\, N \cdot \tfrac{TL}{2\pi}(\ell^2 + L^2/3) = L^2 N \cdot \tfrac{T\ell}{2\pi}$, which is precisely where the paper's $F(\lambda_1)$ with $\lambda_1 = L/\ell_1$ is checked.
--
--   **Role.** The purely arithmetic core of `Zeta23.PrimeSide.ratio` ([eq:ratio]): that theorem instantiates this inequality with the eventual bounds `tr1'`, `tr2`, and [eq:RvM] from the `Facts` record.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L678-L772, docstring tag [eq:ratio]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideTemp

open Real Filter Asymptotics Topology
open Zeta23
open PrimeSide
open PaperParams
variable {P : Params} (D : Data P)
variable {D} (h : Facts D)
include h
omit h

theorem Zeta23.PrimeSide.ratio_pointwise (T L ℓ lT E N G G2 A C₁ C₂ : ℝ)
    (hT : 1 ≤ T) (hL : 0 < L) (hℓ1 : 1 ≤ ℓ) (hℓl : lT ≤ ℓ) (hN0 : 0 < N) (hE0 : 0 ≤ E)
    (hET : 1 / T ≤ E) (hA : 0 ≤ A) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hs1 : C₁ * E ≤ 1 / 2) (hs2 : C₂ * E ≤ 1 / 2) (hTA : 2 * π * A ≤ T)
    (h1 : |G - L * N| ≤ C₁ * (E * (L * N)))
    (h2 : |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)| ≤ C₂ * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))))
    (hN : |N - T * ℓ / (2 * π)| ≤ A * lT) :
    |G ^ 2 / G2 - Ffun (L / ℓ) * N| ≤ 2 * (2 * π * A + 5 * C₁ + C₂) * (E * (Ffun (L / ℓ) * N)) := by sorry
