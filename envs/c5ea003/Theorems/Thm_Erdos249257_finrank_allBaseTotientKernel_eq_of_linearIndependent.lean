-- Prove2me | Theorems.Thm_Erdos249257_finrank_allBaseTotientKernel_eq_of_linearIndependent
-- name    : Erdos249257.finrank_allBaseTotientKernel_eq_of_linearIndependent
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T13:53:37.347896+00:00
-- url     : https://prove2.me/theorems/dda4dfe6-863c-46cc-ac94-a836e652fb75
-- title:
--   Conditional rank of the canonical all-base totient kernel
-- statement:
--   For $k ≥ 2$, the canonical level-$e$ totient family has rank $k^e + 1$ if that family is linearly independent. The independence assumption is part of this theorem.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L1216-L1223
--   Prior mathematical result subsuming the independence ingredient: https://arxiv.org/abs/math/0603053

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

open Erdos249257
open Module Matrix

open Erdos249257

theorem Erdos249257.finrank_allBaseTotientKernel_eq_of_linearIndependent (k e : ℕ) (hk : 2 ≤ k)
    (hli : LinearIndependent ℚ (allBaseCanonicalFamily k e)) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseCanonicalFamily k e))) =
      k ^ e + 1 := by sorry
