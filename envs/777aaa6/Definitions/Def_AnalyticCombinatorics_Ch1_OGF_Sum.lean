-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sum
-- name    : AnalyticCombinatorics_Ch1_OGF_Sum
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:48.282454+00:00
-- url     : https://prove2.me/theorems/a94b62e0-787f-4140-9b7a-abac76aa76bb
-- title:
--   Disjoint unions of graded finite classes
-- statement:
--   For each natural size n, the sum class has size fibre C_n ⊔ D_n. Its finite-type structure is the disjoint union of the two given finite fibres.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Sum.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — The combinatorial sum (disjoint union) construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, first admissible construction.
If `A = B + C` is the disjoint union of two combinatorial classes (an object of
size `n` is a `B`-object of size `n` *or* a `C`-object of size `n`), then the
counting sequences add, `Aₙ = Bₙ + Cₙ`, and hence the OGFs add:

  **`(B + C)(z) = B(z) + C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` identity `counts_sum`; the
generating-function identity `ogf_sum` is its image under `ogfSeq`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The combinatorial sum `B + C`: objects of size `n` are the disjoint union of
the size-`n` objects of `B` and of `C` (F&S §I.2). -/
def CombClass.sum (C D : CombClass) : CombClass where
  Obj n := C.Obj n ⊕ D.Obj n
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


