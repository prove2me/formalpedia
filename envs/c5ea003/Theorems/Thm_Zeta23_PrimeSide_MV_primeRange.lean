-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_MV_primeRange
-- name    : Zeta23.PrimeSide.MV_primeRange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:02:12.090653+00:00
-- url     : https://prove2.me/theorems/0fb8d171-19e9-4e2f-ad41-fd432f2a75df
-- title:
--   Montgomery–Vaughan Hilbert inequality at the frequencies $y_n = \log n$
-- statement:
--   `MVHilbert` $C$ is the hypothesis H-MV [lem:MV]: the Montgomery–Vaughan weighted (generalised) Hilbert inequality with constant $C$, for any finite family of distinct real frequencies with admissible spacings $\delta_r \le |\lambda_r - \lambda_s|$. Here `primeRange` $X$ is the index set of integers $0 < n \le \lfloor X\rfloor$.
--
--   The theorem specialises H-MV to the frequencies $y_n = \log n$ with admissible spacings $\delta_n = 1/(2n)$ (since $|\log n - \log m| \ge 1/(2\max(n,m))$ for $n \ne m$): for every real $X$ and all complex weights $x, z \colon \mathbb N \to \mathbb C$,
--   $$\Bigl\|\sum_{\substack{n,m \le X \\ n \ne m}} \frac{x_n\,\overline{z_m}}{\log n - \log m}\Bigr\| \;\le\; C\,\Bigl(\sum_{n \le X} 2n\,\|x_n\|^2\Bigr)^{1/2}\Bigl(\sum_{n \le X} 2n\,\|z_n\|^2\Bigr)^{1/2}.$$
--   The sums run over all integers $n \le X$, not only prime powers — harmless, since the intended weights carry a factor $\Lambda(n)$ ([lem:MV] with [eq:deltan], §5.1).
--
--   It feeds `MV_real`, the real cosine/sine form used for the off-diagonal term $\mathcal O_1$ of the $P\times P$ second-moment contribution (module `Zeta23.PrimeSideB.PPKernel`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L561-L602, docstring tags [lem:MV], [eq:deltan]

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

theorem Zeta23.PrimeSide.MV_primeRange (hMV : Zeta23.MVHilbert C) (X : ℝ) (x z : ℕ → ℂ) :
    ‖∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))‖
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, ‖x n‖ ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, ‖z n‖ ^ 2 * (2 * n)) := by sorry
