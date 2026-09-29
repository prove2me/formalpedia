-- Prove2me | Theorems.Thm_Erdos249257_finrank_allBaseThroughLevelFamily_eq
-- name    : Erdos249257.finrank_allBaseThroughLevelFamily_eq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T13:53:41.467953+00:00
-- url     : https://prove2.me/theorems/932aa16c-3571-4c0a-88d4-dc548e182c68
-- title:
--   Rank of the complete all-base totient truncation
-- statement:
--   For $k ≥ 2$ and $e ≥ 1$, the rational span of all totient sections through level $e$ has dimension $k^e + 1$. The source obtains this from canonical-family independence and spanning reduction.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/AllBaseTotientKernel.lean#L1233-L1239
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

theorem Erdos249257.finrank_allBaseThroughLevelFamily_eq (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))) =
      k ^ e + 1 := by sorry
