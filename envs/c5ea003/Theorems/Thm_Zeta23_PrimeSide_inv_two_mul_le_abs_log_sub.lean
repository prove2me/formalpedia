-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_inv_two_mul_le_abs_log_sub
-- name    : Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:01:16.94307+00:00
-- url     : https://prove2.me/theorems/13039dae-5ffb-44db-ac48-03ba469be9b5
-- title:
--   Logarithmic spacing of integers: $\tfrac{1}{2n} \le |\log n - \log m|$ for $n \ne m$
-- statement:
--   Let $n,m\ge 1$ be natural numbers with $n\ne m$. Then
--   $$\frac{1}{2n}\ \le\ \bigl|\log n-\log m\bigr|.$$
--
--   This is the paper's [eq:deltan] (§5.1) — "consecutive prime powers $n<n'$ satisfy $\log(n'/n)\ge\log((n+1)/n)\ge 1/(2n)$, so $\delta_n^{-1}\le 2n$" — recast in the admissible-weight form required by the Montgomery–Vaughan generalised Hilbert inequality (H-MV): the frequencies $\log n$ are separated by at least the weights $\delta_n=1/(2n)$, and no primality is needed since the statement holds for all distinct integers $n,m\ge 1$.
--
--   In the project (module `Zeta23.PrimeSideB.PPKernel`) it is consumed by `MV_primeRange`, the instantiation of the weighted Hilbert inequality on the prime-power frequencies $\{\log n : n\le X\}$, which controls the off-diagonal sums $\mathcal{O}_1,\mathcal{O}_2$ in the proof of [prop:PP].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L528-L559, docstring tag [eq:deltan]

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

theorem Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : n ≠ m) :
    1 / (2 * (n:ℝ)) ≤ |Real.log n - Real.log m| := by sorry
