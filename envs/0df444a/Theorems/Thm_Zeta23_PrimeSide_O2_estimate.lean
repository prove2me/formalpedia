-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_O2_estimate
-- name    : Zeta23.PrimeSide.O2_estimate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:05:44.23362+00:00
-- url     : https://prove2.me/theorems/5d754988-52b0-4c1c-923d-cda214292362
-- title:
--   Sum-frequency bound $|\mathcal O_2| \le \frac{\int\Phi^2}{\log 2}\bigl(\sum_{n\le X} a_n\bigr)^2$
-- statement:
--   Let $\Phi$ be continuous with $\Phi^2$ integrable, and let $X, T$ be real. Write $a_n = \Lambda(n)/\sqrt n$, $y_n = \log n$, and let $A^+$ (`Aplus`) be the sum-frequency half of the kernel $\mathcal M[\cos(\cdot\,y_n),\cos(\cdot\,y_m)]$.
--
--   Then the term $\mathcal O_2$ of the decomposition [eq:MPP] satisfies
--   $$\Bigl|\sum_{n, m \le X} a_n a_m\,A^+(y_n, y_m)\Bigr| \;\le\; \frac{\int_{\mathbb R}\Phi(x)^2\,dx}{\log 2}\,\Bigl(\sum_{n \le X} a_n\Bigr)^2,$$
--   sums over integers $0 < n,m \le \lfloor X\rfloor$. Terms with $n = 1$ or $m = 1$ vanish since $\Lambda(1) = 0$; for the rest $y_n + y_m \ge 2\log 2$, so the per-pair bound $|A^+(y,y')| \le \frac{2}{y+y'}\int\Phi^2$ (`abs_Aplus_le`, §5.4's "$|\int (nm)^{i\tau'}d\tau'| \le 2/\log(nm)$") applies. This is the pre-Chebyshev form of "$|\mathcal O_2| \ll XL$".
--
--   It feeds `prop_PP`, the evaluation of the $P\times P$ contribution to the mollified second moment.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PP.lean#L278-L319

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

theorem Zeta23.PrimeSide.O2_estimate (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X T : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, acoef n * acoef m * Aplus Φ T (Real.log n) (Real.log m)|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by sorry
