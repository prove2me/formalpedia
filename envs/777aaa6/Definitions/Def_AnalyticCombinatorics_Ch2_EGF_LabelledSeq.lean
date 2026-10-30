-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledSeq
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:34:09.07211+00:00
-- url     : https://prove2.me/theorems/7d66a5c9-e251-4a8d-be2d-7d6b648dee31
-- title:
--   Labelled sequences with a bounded component count
-- statement:
--   A size-n object chooses an integer k with 0≤k≤n and an object of the k-fold labelled power. When components have no size-zero objects, this bounded construction represents all finite labelled sequences of total size n. The foundation also defines the discrete topology on the rational coefficient field; its instance is local to the source section.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledSeq.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch2 §II.1 — The labelled sequence construction

Flajolet & Sedgewick, Part A, Chapter II. `SEQ(C)` is the disjoint union of all
labelled powers `C^{⋆k}`. When `C₀=∅`, only powers `k ≤ n` contribute to size `n`,
and the EGF is the geometric series

  `SEQ(C)(z) = 1 / (1 - C(z))`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The labelled sequence construction `SEQ(C)`: a size-`n` object is a `k`-fold
labelled power of `C`, for some `0 ≤ k ≤ n`. The hypothesis `C₀=∅` is used in the
EGF theorem, where powers with `k > n` have zero `n`th coefficient. -/
def CombClass.lseq (C : CombClass) : CombClass where
  Obj n := Σ k : Fin (n + 1), (C.lpow k).Obj n
  finObj _ := inferInstance

section EGF

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatLseq : TopologicalSpace ℚ := ⊥

end EGF

end AnalyticCombinatorics.Ch1


