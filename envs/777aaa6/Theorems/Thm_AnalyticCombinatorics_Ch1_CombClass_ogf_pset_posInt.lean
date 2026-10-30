-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_CombClass_ogf_pset_posInt
-- name    : AnalyticCombinatorics.Ch1.CombClass.ogf_pset_posInt
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:30.107871+00:00
-- url     : https://prove2.me/theorems/50bc7c61-3df4-43f1-99e7-8967836449f2
-- title:
--   Generating function of distinct positive parts
-- statement:
--   Let $D_n$ be the source powerset construction on the class with one object of each positive size: equivalently, a partition of $n$ decorated by a subset of the singleton object set at each positive size, of cardinality equal to that size multiplicity. Every multiplicity is therefore zero or one. Then
--
--   $$\sum_{n\ge0}|D_n|z^n=\prod_{m\ge1}(1+z^m).$$
--
--   The equality is coefficientwise over $\mathbb Q$ with discrete coefficient topology.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/DistinctPartitions.lean#L29. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pset
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_DistinctPartitions
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

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatDistinct

local instance _root_.AnalyticCombinatorics.Ch1.instDiscRatDistinct : DiscreteTopology ℚ := ⟨rfl⟩

theorem AnalyticCombinatorics.Ch1.CombClass.ogf_pset_posInt :
    CombClass.posInt.pset.ogf = ∏' i, (1 + (X : ℚ⟦X⟧) ^ (i + 1)) := by sorry
