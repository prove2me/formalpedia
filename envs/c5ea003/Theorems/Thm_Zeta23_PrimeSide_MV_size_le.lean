-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_MV_size_le
-- name    : Zeta23.PrimeSide.MV_size_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:02:29.934668+00:00
-- url     : https://prove2.me/theorems/16602d55-86e0-4426-9286-130191496bdc
-- title:
--   Size of the Montgomery–Vaughan bound for the weights $a_n = \Lambda(n)/\sqrt n$
-- statement:
--   Here $a_n = \Lambda(n)/\sqrt n$ (`acoef`, with $\Lambda$ the von Mangoldt function), and sums run over integers $0 < n \le \lfloor X\rfloor$. Assume $C \ge 0$, $W \ge 0$, and let $w \colon \mathbb N \to \mathbb R$ satisfy $|w_n| \le W$ for all $n \le X$.
--
--   Then the right-hand side of the Montgomery–Vaughan bound with weights $u = a$ and $v = a\,w$ is controlled by the pure $\Lambda^2$-sum:
--   $$C\Bigl(\sum_{n \le X} 2n\,a_n^2\Bigr)^{1/2}\Bigl(\sum_{n \le X} 2n\,(a_n w_n)^2\Bigr)^{1/2} \;\le\; 2\,C\,W \sum_{n \le X} \Lambda(n)^2,$$
--   and likewise with the two square-root factors in the opposite order (the statement is a conjunction of both). The point is that $2n\,a_n^2 = 2\Lambda(n)^2$, so each factor is at most $\sqrt{2\sum\Lambda(n)^2}$, respectively $W\sqrt{2\sum\Lambda(n)^2}$. This is §5.4's "each of the four is at most $(3\pi/2)\cdot\pi L\cdot\sum_n a_n^2/\delta_n \ll L^2 X$" in pre-Chebyshev form.
--
--   It is consumed by `O1_bound` to convert the Hilbert-inequality bound for $\mathcal O_1$ into the final $\sum \Lambda(n)^2$ form.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L667-L709

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
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {C : ℝ}

theorem Zeta23.PrimeSide.MV_size_le (hC : 0 ≤ C) (X : ℝ) {w : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw : ∀ n ∈ primeRange X, |w n| ≤ W) :
    C * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ∧
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, acoef n ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by sorry
