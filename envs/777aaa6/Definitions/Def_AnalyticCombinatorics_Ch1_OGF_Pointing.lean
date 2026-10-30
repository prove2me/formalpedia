-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pointing
-- name    : AnalyticCombinatorics_Ch1_OGF_Pointing
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:59.418211+00:00
-- url     : https://prove2.me/theorems/1f68c663-55ba-4954-9cfc-9726a0cc3652
-- title:
--   Pointed graded objects
-- statement:
--   A size-n pointed object is a pair of a C-object of size n and an index in Fin n. The size-zero fibre is empty. This is a finite choice model for the formal pointing operator.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Pointing.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.6 — The pointing construction Θ

Flajolet & Sedgewick, Part A, Chapter I. The *pointing* of a class `C`,
`Θ(C)`, distinguishes one of the `n` atoms of a size-`n` object: a pointed object
is a `C`-object together with a choice of one of its `n` atoms. Hence
`Θ(C)ₙ = n·Cₙ`, and the OGF is

  **`Θ(C)(z) = z·C'(z)`**

(the operator `z d/dz`). We model the pointed objects by `C.Obj n × Fin n`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The pointing construction `Θ(C)` (F&S §I.6): a size-`n` object is a `C`-object
together with a distinguished atom (one of its `n` atoms), modelled as
`C.Obj n × Fin n`. -/
def CombClass.pointing (C : CombClass) : CombClass where
  Obj n := C.Obj n × Fin n
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


