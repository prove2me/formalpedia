-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_Tauberian
-- name    : AnalyticCombinatorics_Ch8_Partitions_Tauberian
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T13:48:11.345985+00:00
-- url     : https://prove2.me/theorems/83dbaa96-5a04-4ada-8d6b-7e85bb2c976e
-- title:
--   Tauberian mathematical objects
-- statement:
--   For any real sequence a and natural N, Cum(a,N) is the finite sum of a(n) from n=0 through N, inclusive; no sign assumption on a is part of this definition.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/Tauberian.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# A logarithmic Tauberian theorem for cumulative coefficients

This file is intentionally independent of the partition development.  The
results are stated for an arbitrary nonnegative sequence of real coefficients.
-/

open Filter
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Tauberian

noncomputable section

/-- Cumulative sums of a sequence. -/
def Cum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), a n

end

end AnalyticCombinatorics.Ch8.Partitions.Tauberian


