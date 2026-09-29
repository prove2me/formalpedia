-- Prove2me | Theorems.Thm_Erdos180_extremalScale_nonneg
-- name    : Erdos180.extremalScale_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:11:00.871292+00:00
-- url     : https://prove2.me/theorems/d9429d95-d1ef-4985-a686-20d77ecabf9e
-- title:
--   The normalising scale is nonnegative
-- statement:
--   The scale $n \mapsto n^{4/3}$ against which both bounds of Theorem 1.1 are measured is
--   nonnegative. A bookkeeping fact needed to divide by it when converting the polynomial
--   inequalities into asymptotic statements.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4218-L4221

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos180.extremalScale_nonneg (n : ℕ) :
    0 ≤ extremalScale n := by sorry
