-- Prove2me | Theorems.Thm_trunc_nonneg
-- name    : trunc.nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:17:09.205848+00:00
-- url     : https://prove2.me/theorems/13ad6031-737d-41b5-81fb-75d6e8a686ef
-- title:
--   trunc: nonneg
-- statement:
--   The trunc construction uses the nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L134-L134
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L134-L134

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open trunc

theorem trunc.nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := by sorry
