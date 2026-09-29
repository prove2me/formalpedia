-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_O1_bound
-- name    : Zeta23.PrimeSide.O1_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:05:10.463749+00:00
-- url     : https://prove2.me/theorems/dd6ef794-04fe-419b-82b6-af211f47dffa
-- title:
--   Off-diagonal bound $|\mathcal O_1| \le 16\,C\,(\int\Phi^2)\sum_{n\le X}\Lambda(n)^2$
-- statement:
--   Assume the Montgomery–Vaughan hypothesis `MVHilbert` $C$ with $C \ge 0$, let $T \ge 0$, and let $\Phi$ be continuous with $\Phi^2$ integrable. Write $a_n = \Lambda(n)/\sqrt n$, and let $A^-$ (`Aminus`) be the difference-frequency half of the kernel $\mathcal M[\cos(\cdot\,y_n), \cos(\cdot\,y_m)]$ from `PPKernel`.
--
--   Then for every real $X$, the off-diagonal term $\mathcal O_1$ of the decomposition [eq:MPP] satisfies
--   $$\Bigl|\sum_{\substack{n,m \le X\\ n \ne m}} a_n a_m\,A^-(\log n, \log m)\Bigr| \;\le\; 16\,C\,\Bigl(\int_{\mathbb R}\Phi(x)^2\,dx\Bigr)\sum_{n \le X}\Lambda(n)^2,$$
--   sums over integers $0 < n, m \le \lfloor X\rfloor$. This is §5.4's "Hence $|\mathcal O_1| \ll L^2 X$" in pre-Chebyshev form: unfolding $A^-$ produces four bilinear sums of Hilbert type, each bounded via `MV_real` and `MV_size_le`.
--
--   It is one of the three estimates feeding `prop_PP`, the evaluation of the $P \times P$ contribution to the mollified second moment (module `Zeta23.PrimeSideB.PPOffDiag`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPOffDiag.lean#L36-L170, docstring tag [prop:PP]

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
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide

theorem Zeta23.PrimeSide.O1_bound {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) {Φ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (X : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℝ) else acoef n * acoef m * Aminus Φ T (Real.log n) (Real.log m))|
      ≤ 16 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by sorry
