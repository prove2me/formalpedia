-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_partitions
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_partitions
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:25.160371+00:00
-- url     : https://prove2.me/theorems/c4d4827a-331d-4344-9e41-e8a152aa85ca
-- title:
--   Euler product for integer partitions
-- statement:
--   Let $p(n)$ be the cardinality of the source type `Nat.Partition n`, whose elements are multisets of positive integers summing to $n$. In formal power series over $\mathbb Q$,
--
--   $$\sum_{n\ge0}p(n)z^n=\prod_{m\ge1}\left(\sum_{j\ge0}z^{mj}\right).$$
--
--   The sums and product use coefficientwise formal-series convergence with discrete rational coefficients; this is not an analytic infinite-product assertion.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Partitions.lean#L52. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Partitions
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — Integer partitions and Euler's product (MSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. An integer partition of `n` is a
multiset of positive integers summing to `n` — i.e. an object of `MSET(ℙ)` of size
`n`. Its generating function is Euler's product

  `P(z) = ∏_{m≥1} 1/(1 - z^m) = ∏_{m≥1} ∑_{j≥0} z^{m j}`.

We model the partition class with Mathlib's `Nat.Partition` (a `Fintype`), connect
its OGF to Mathlib's `Nat.Partition.genFun`, and push it to the explicit infinite
product. The literal Euler product is an explicit TODO in Mathlib's `GenFun`, so
this is genuinely new content; it is anchored on `#(Nat.Partition n)`. The infinite
product/sums use the X-adic (coefficientwise) topology on `ℚ⟦X⟧`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatPartitions

local instance _root_.AnalyticCombinatorics.Ch1.instDiscRatPartitions : DiscreteTopology ℚ := ⟨rfl⟩

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_partitions :
    CombClass.partitions.ogf
      = ∏' i, ∑' j, (X : ℚ⟦X⟧) ^ ((i + 1) * j) := by sorry
