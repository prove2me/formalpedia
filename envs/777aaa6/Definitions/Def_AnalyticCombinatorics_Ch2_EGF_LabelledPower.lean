-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledPower
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:33:42.838213+00:00
-- url     : https://prove2.me/theorems/c08182a9-9eeb-4fbc-b8bf-183888859b75
-- title:
--   Finite iterated labelled products
-- statement:
--   The zeroth labelled power is the single empty object. A positive labelled power is formed by repeating the labelled product, retaining the ordered list of component factors and the original total label size.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledPower.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
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
# Ch2 §II.1 — Labelled powers

Flajolet & Sedgewick, Part A, Chapter II. Iterating the labelled product gives the
`k`-th labelled power `C^{⋆k}`, with EGF `C(z)^k` (an immediate induction from the
labelled product rule). The neutral class `ε` is the unit, with EGF `1`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The `k`-fold labelled power `C^{⋆k} = C ⋆ (C ⋆ ⋯)` (F&S §II.1). -/
def CombClass.lpow (C : CombClass) : ℕ → CombClass
  | 0 => CombClass.neutral
  | (k + 1) => C.lprod (C.lpow k)

end AnalyticCombinatorics.Ch1


