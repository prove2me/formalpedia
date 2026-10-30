-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_DistinctPartitions
-- name    : AnalyticCombinatorics_Ch1_OGF_DistinctPartitions
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:38.133262+00:00
-- url     : https://prove2.me/theorems/c61badd9-08eb-43d6-a658-5cbd94c1455f
-- title:
--   Positive-size finite subsets and coefficientwise products
-- statement:
--   The underlying class is the size-grouped powerset of the positive-integer class, with one potential object at every positive size. The rational coefficient topology is discrete, so formal infinite products are interpreted coefficientwise.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/DistinctPartitions.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Fintype.Powerset
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.3 — Partitions into distinct parts (PSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. A partition of `n` into *distinct*
parts is a set of distinct positive integers summing to `n` — an object of
`PSET(ℙ)` of size `n`. Specializing the general powerset transfer `ogf_pset` to the
positive-integer class `ℙ` (`Cₘ=1`, `choose 1 k` supported on `{0,1}`) gives the
classical generating function

  `D(z) = ∏_{m≥1} (1 + z^m)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

section
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatDistinct : TopologicalSpace ℚ := ⊥

end

end AnalyticCombinatorics.Ch1


