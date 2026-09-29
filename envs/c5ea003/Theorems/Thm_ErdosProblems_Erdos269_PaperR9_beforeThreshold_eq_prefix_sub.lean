-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperR9_beforeThreshold_eq_prefix_sub
-- name    : ErdosProblems.Erdos269.PaperR9.beforeThreshold_eq_prefix_sub
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:16:56.509334+00:00
-- url     : https://prove2.me/theorems/67a91e9b-5995-4f95-ac41-990201fc317c
-- title:
--   BeforeThreshold eq prefix sub
-- statement:
--   The count of dyadic shell points below a pure p-power threshold is the truncated difference of cumulative strict smooth counts at the threshold and the dyadic lower endpoint.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR9SourceCounts.lean#L281-L309
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact source-count normalisation for certificate reconstruction

This module does not certify a generated list by fiat. It starts with the
library's actual strictSmoothPairs / strictSmoothExponents and proves the
one-dimensional pair count, cumulative pure-power count, threshold difference,
and complete ordered dyadic digit formula.

The executable pair evaluator uses successive division. It does not enumerate
a box of side `x` or compute real logarithms. Its boundary sweep is linear in the two exponent bounds. No unproved
logarithmic-interval or Euclidean floor-sum optimisation is used by this return.

Source APIs reused: RestrictedFloorSum.lean, strictSmoothShell_card,
restrictedPurePowerCount_eq_restrictedLogFloorSum, restrictedLogFloorSum_succ_sub;
Mathlib/Data/Nat/Log.lean; Lean src/Init/Data/Nat/Div/Basic.lean.
Finset.card_eq_sum_card_fiberwise is reused exactly as in the supplied
RestrictedFloorSum.lean:332.

-/
open Finset

open ErdosProblems.Erdos269.PaperR9

theorem ErdosProblems.Erdos269.PaperR9.beforeThreshold_eq_prefix_sub (p a : ℕ) :
    dyadicBeforeThresholdCount235 p a =
      smoothCountLT 2 3 5 (p ^ Nat.log p (2 ^ (a + 1))) -
        smoothCountLT 2 3 5 (2 ^ a) := by sorry
