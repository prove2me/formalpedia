-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Partitions
-- name    : AnalyticCombinatorics_Ch1_OGF_Partitions
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:54.465074+00:00
-- url     : https://prove2.me/theorems/589d8ce0-6e5e-418d-8974-5f9dd95c2cfa
-- title:
--   The finite class of integer partitions
-- statement:
--   The size-n fibre is Nat.Partition n, the finite type of multisets of positive integers summing to n. Its ordinary generating function has those cardinalities as rational coefficients. Rational coefficients are given the discrete topology for coefficientwise infinite sums and products.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Partitions.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
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

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The class of integer partitions (F&S §I.3): an object of size `n` is a
partition of `n` (a multiset of positive integers summing to `n`). This is
Mathlib's `Nat.Partition n`. -/
def CombClass.partitions : CombClass where
  Obj n := Nat.Partition n
  finObj _ := inferInstance

@[simp] lemma CombClass.counts_partitions (n : ℕ) :
    CombClass.partitions.counts n = Fintype.card (Nat.Partition n) := rfl

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatPartitions : TopologicalSpace ℚ := ⊥

end EulerProduct

end AnalyticCombinatorics.Ch1


