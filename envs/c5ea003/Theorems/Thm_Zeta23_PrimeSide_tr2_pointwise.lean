-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_tr2_pointwise
-- name    : Zeta23.PrimeSide.tr2_pointwise
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:37:50.7605+00:00
-- url     : https://prove2.me/theorems/66897a76-9715-4a56-9770-fc166390104c
-- title:
--   Pointwise arithmetic behind [eq:tr2]: checking the constant $\ell_1^2 + L^2/3$
-- statement:
--   A purely arithmetic inequality between real numbers, isolating the constant-checking behind the second form of [eq:tr2]: every quantity is a plain real variable, and all analytic content enters through hypotheses.
--
--   **Setup.** Let $T, L, \ell, l, X, E, S, I_2, b, G_2, w, C_R, C_\mu, C_u, C_l$ be real numbers. Assume the range conditions $T, L, l, X \ge 1$, $\log l \ge 1$, $l \le \ell$, $L \le l$, $1 \le w$, $2w \le L$, and $1 - 2w/L \le b \le 1$; assume $E \ge 0$ dominates both $w/L$ and $(l^2 + X)\log l/(T l)$; and assume the four analytic inputs, with nonnegative constants $C_R, C_\mu, C_u, C_l$:
--
--   $$\bigl|G_2 - \bigl(2\pi b L I_2 + \tfrac{T}{\pi} S\bigr)\bigr| \le C_R\, L\, l\, (\log l)\,(l^2 + X), \qquad \Bigl|I_2 - \frac{T \ell^2}{4\pi^2}\Bigr| \le C_\mu\, \frac{T\ell^2}{4\pi^2}\,\frac{1}{l^2},$$
--
--   $$S - \frac{L^3}{6} \le C_u L^2, \qquad -C_l L^2 \le S - \frac{(L - 2w)^3}{6}.$$
--
--   (Here $G_2$ plays the role of $\operatorname{tr}\tilde G^2$, $I_2$ of $\int_T^{2T}\mu^2$, $S$ of the prime sum $\sum_n a_n^2 g(y_n)$, and $\ell$ of $\ell_1$.)
--
--   **Statement.** Then
--
--   $$\Bigl|G_2 - \frac{T L}{2\pi}\Bigl(\ell^2 + \frac{L^2}{3}\Bigr)\Bigr| \;\le\; \bigl(2\pi C_R + C_\mu + 2 + 6(C_u + C_l + 2w)\bigr)\cdot E \cdot \frac{T L}{2\pi}\Bigl(\ell^2 + \frac{L^2}{3}\Bigr).$$
--
--   **Role.** This is the elementary core of `Zeta23.PrimeSide.tr2` in `Zeta23.PrimeSideB`: applied with the `EvBound` hypotheses of `Facts D` instantiated at large $T$, it converts the first form of [eq:tr2] plus the $\mu$-moment and prime-sum estimates into the asymptotic $\operatorname{tr}\tilde G^2 = \frac{TL}{2\pi}(\ell_1^2 + L^2/3)(1 + O(\mathcal{E}_T))$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB.lean#L542-L651, docstring tag [eq:tr2]

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

theorem Zeta23.PrimeSide.tr2_pointwise (T L ℓ lT X E S I2 b G2 w CR Cμ Cu Cl : ℝ)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hl : 1 ≤ lT) (hlog : 1 ≤ Real.log lT) (hX : 1 ≤ X)
    (hℓl : lT ≤ ℓ) (hLl : L ≤ lT) (hw : 1 ≤ w) (hL2w : 2 * w ≤ L) (hb1 : 1 - 2 * w / L ≤ b) (hble1 : b ≤ 1)
    (hE0 : 0 ≤ E) (hEw : w / L ≤ E) (hEmid : (lT ^ 2 + X) * Real.log lT / (T * lT) ≤ E)
    (hCR : 0 ≤ CR) (hCμ : 0 ≤ Cμ) (hCu : 0 ≤ Cu) (hCl : 0 ≤ Cl)
    (hR : |G2 - (2 * π * b * L * I2 + T / π * S)| ≤ CR * (L * lT * Real.log lT * (lT ^ 2 + X)))
    (hμ : |I2 - T * ℓ ^ 2 / (4 * π ^ 2)| ≤ Cμ * (T * ℓ ^ 2 / (4 * π ^ 2) / lT ^ 2))
    (hSup : S - L ^ 3 / 6 ≤ Cu * L ^ 2) (hSlo : -(Cl * L ^ 2) ≤ S - (L - 2 * w) ^ 3 / 6) :
    |G2 - T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3)|
      ≤ (2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * w)) * (E * (T * L / (2 * π) * (ℓ ^ 2 + L ^ 2 / 3))) := by sorry
