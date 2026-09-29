-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_diag_estimate
-- name    : Zeta23.PrimeSide.diag_estimate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:24:08.90847+00:00
-- url     : https://prove2.me/theorems/634edef0-4d37-44ef-84bf-5af4c50e7092
-- title:
--   The diagonal estimate $\mathcal{D}$: main term of the prime–prime sum
-- statement:
--   Here $a_n = \Lambda(n)/\sqrt{n}$ and $y_n = \log n$ (with $\Lambda$ the von Mangoldt function), the sum ranges over `primeRange` $X$ = integers $0 < n \le \lfloor X \rfloor$ (so effectively over prime powers $n \le X$), and $\mathrm{sumA2g}(X, g) = \sum_{n \le X} \Lambda(n)^2 n^{-1}\, g(\log n) = \sum_n a_n^2 g(y_n)$. The kernel $A^-(y, y') = \int_{[-T,T]} \Phi(x)^2\, J(y - y',\, xy)\, dx$ is the difference-frequency half of $\mathcal{M}[\cos(\cdot\, y), \cos(\cdot\, y')]$, where $J$ is the closed form of $\int \cos(\theta t + c)\, dt$ over the sheared window $I \cap (I - x)$. Assume $T \ge 0$, $\Phi$ continuous with $\Phi^2$ and $\Phi^2 |x|$ integrable, and the Fourier identity [eq:Phi2FT]: $\int_{\mathbb{R}} \Phi(x)^2 \cos(xy)\, dx = 2\pi g(y)$ for all $y$. Then for every $X$,
--   $$\Bigl|\frac{1}{2\pi^2} \sum_{n \le X} a_n^2\, A^-(y_n, y_n) \;-\; \frac{T}{\pi} \sum_{n \le X} a_n^2\, g(y_n)\Bigr| \;\le\; \frac{1}{2\pi^2} \Bigl(\sum_{n \le X} a_n^2\Bigr) \int_{\mathbb{R}} \Phi(x)^2\, |x|\, dx.$$
--   This is the estimate $\mathcal{D}$ of Section 5.4: on the diagonal $y = y'$ the inner integral is the window length $T - |x|$, whose main term $T$ produces $2\pi g(y_n)$ by [eq:Phi2FT] and whose defect $|x|$ produces the stated error, uniformly per $n$.
--
--   It supplies the main term of `prop_PP`, the evaluation $\mathcal{M}[P_X, P_X] = (T/\pi) \sum_{n \le X} \Lambda(n)^2 n^{-1} g(\log n) + O(L^2 X)$ of [prop:PP] (module `Zeta23.PrimeSideB.PP`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L247-L276, docstring tag [eq:Phi2FT]

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
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.diag_estimate (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) {g : ℝ → ℝ}
    (hFT : ∀ y, ∫ x, Φ x ^ 2 * Real.cos (x * y) = 2 * π * g y) (X : ℝ) :
    |(1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2 * Aminus Φ T (Real.log n) (Real.log n))
        - T / π * sumA2g X g|
      ≤ (1 / (2 * π ^ 2)) * (∑ n ∈ primeRange X, acoef n ^ 2) * ∫ x, Φ x ^ 2 * |x| := by sorry
