-- Prove2me | Theorems.Thm_Erdos180_manuscriptLowerConstant_pos
-- name    : Erdos180.manuscriptLowerConstant_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:11:20.475295+00:00
-- url     : https://prove2.me/theorems/110da033-f9d9-4870-94b4-e115b6814230
-- title:
--   The lower-bound constant is positive
-- statement:
--   The explicit constant $c$ in $\mathrm{ex}(n,F) \ge c\,n^{4/3}$ is strictly positive.
--
--   Its value is $2^{-4/3} \cdot 27^{-4/3}$, coming from equation (8) of the source together with
--   the loss $n_{tq} \le t^3 n_q$ incurred when rounding the prime power $q$ down. Theorem 1.1
--   asserts $\mathrm{ex}(n,F) = \Omega(n^{4/3})$, so positivity of $c$ is part of the claim.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L4244-L4246

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Erdos180
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos180.manuscriptLowerConstant_pos : 0 < manuscriptLowerConstant := by sorry
