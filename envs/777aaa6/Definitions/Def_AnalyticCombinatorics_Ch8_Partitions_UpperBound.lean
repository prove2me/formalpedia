-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
-- name    : AnalyticCombinatorics_Ch8_Partitions_UpperBound
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:47:49.676389+00:00
-- url     : https://prove2.me/theorems/4549a3c5-6062-44ed-87eb-680baec4f31a
-- title:
--   Upper Bound mathematical objects
-- statement:
--   For each natural n, part(n) is the number of unordered partitions of n into positive integer parts, cast to a real number. A is the real constant pi^2/6.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/UpperBound.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


namespace AnalyticCombinatorics.Ch8.Partitions

open scoped BigOperators

noncomputable def part (n : ℕ) : ℝ :=
  (Fintype.card (Nat.Partition n) : ℝ)

noncomputable def A : ℝ :=
  Real.pi ^ 2 / 6

end AnalyticCombinatorics.Ch8.Partitions


