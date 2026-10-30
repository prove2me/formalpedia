-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledSet
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:33:01.120497+00:00
-- url     : https://prove2.me/theorems/5539035b-ab98-4d7d-99ca-1827bf22ce8b
-- title:
--   Set partitions with component decorations
-- statement:
--   A size-n object is a partition of the n labels into nonempty unordered blocks, with one component object of size equal to each block cardinality. The unique empty partition and empty decoration family give the size-zero object.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledSet.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch2 §II.2 — The labelled set construction SET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter II. `SET(C)` forms *sets* of labelled
C-objects (`C₀=∅`): a set partition of the `n` labels into blocks, each block
carrying a C-structure on its labels. Hence

  `SET(C)ₙ = ∑_{π : set partition of [n]} ∏_{B∈π} C_{|B|}`   (exponential formula),

and the EGF is `exp(C(z))`. This file builds the graded `Fintype` model and the
counting identity; the EGF identity is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The labelled set construction `SET(C)` (F&S §II.2): a set partition `π` of the
`n` labels, together with a C-structure on each block. Faithful when `C₀=∅`. -/
noncomputable def CombClass.set (C : CombClass) : CombClass where
  Obj n := Σ π : Finpartition (Finset.univ : Finset (Fin n)),
    ∀ B : π.parts, C.Obj (B.val.card)
  finObj _ := by classical infer_instance

end AnalyticCombinatorics.Ch1


