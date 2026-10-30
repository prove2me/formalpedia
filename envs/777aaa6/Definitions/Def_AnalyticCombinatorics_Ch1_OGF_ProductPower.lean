-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_ProductPower
-- name    : AnalyticCombinatorics_Ch1_OGF_ProductPower
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:45.50665+00:00
-- url     : https://prove2.me/theorems/cd8836c6-00c3-4e7a-83ed-88119db910d9
-- title:
--   Finite Cartesian powers and alphabets
-- statement:
--   The zeroth Cartesian power is the neutral class with one size-zero object, and each successor multiplies by C using additive sizes. The alphabet class has a prescribed finite number a of objects in size one and none elsewhere.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/ProductPower.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Product
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2–I.3 — Cartesian powers and words over a finite alphabet

Flajolet & Sedgewick, Part A, Chapter I. Iterating the product construction gives
the `k`-fold Cartesian power `C^k = C × C × ⋯ × C`, with OGF `C(z)^k` (an immediate
induction from the binary product rule `ogf_prod`). As the standard application,
words of length `k` over an alphabet of `a` letters form `(a·Z)^k`, with OGF
`(a z)^k` (so there are `a^k` of them), recovering F&S §I.3.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The `k`-fold Cartesian power `C^k = C × (C × (⋯))` (F&S §I.2). -/
def CombClass.prodPow (C : CombClass) : ℕ → CombClass
  | 0 => CombClass.neutral
  | (k + 1) => C.prod (C.prodPow k)

/-- The alphabet class on `a` letters: `a` distinct objects of size `1`
(F&S §I.3). Its OGF is `a·z`. -/
def CombClass.alphabet (a : ℕ) : CombClass where
  Obj n := Fin (if n = 1 then a else 0)
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


