-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_MV_real
-- name    : Zeta23.PrimeSide.MV_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:01:54.619674+00:00
-- url     : https://prove2.me/theorems/17de38d1-70b6-41cd-b679-336d03d49242
-- title:
--   Real cosine and sine forms of the Montgomery–Vaughan bilinear bound
-- statement:
--   Assume the Montgomery–Vaughan hypothesis `MVHilbert` $C$ (H-MV, [lem:MV]). Let $X$ be real, $c$ a real phase, and $u, v \colon \mathbb N \to \mathbb R$ real weights; sums run over integers $0 < n \le \lfloor X\rfloor$ (`primeRange` $X$).
--
--   Then both the cosine and the sine bilinear sums obey the Hilbert-type bound: writing $y_n = \log n$,
--   $$\Bigl|\sum_{n \ne m} \frac{u_n v_m \cos\bigl(c\,(y_n - y_m)\bigr)}{y_n - y_m}\Bigr| \;\le\; C\Bigl(\sum_n 2n\,u_n^2\Bigr)^{1/2}\Bigl(\sum_n 2n\,v_n^2\Bigr)^{1/2},$$
--   and the same bound with $\sin$ in place of $\cos$. These are the real and imaginary parts of the complex form `MV_primeRange` applied to the twisted weights $x_n = u_n e^{icy_n}$, $z_m = v_m e^{icy_m}$ (§5.4: the four sums such as $\sum_{n\ne m} (a_n n^{2iT})\,\overline{a_m m^{2iT}\alpha_m^+}/(y_n-y_m)$).
--
--   It is consumed by `O1_bound`, the estimate for the off-diagonal difference-frequency term $\mathcal O_1$ in the $P \times P$ part of the mollified second moment.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L604-L665

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

theorem Zeta23.PrimeSide.MV_real (hMV : Zeta23.MVHilbert C) (X c : ℝ) (u v : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) := by sorry
