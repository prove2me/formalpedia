-- Prove2me | Theorems.Thm_Fpy_sumVal_mem
-- name    : Fpy.sumVal_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:07:55.857136+00:00
-- url     : https://prove2.me/theorems/f0ca49d1-92b2-41c5-b167-cd223fd95b2b
-- title:
--   Fpy: sum Val mem
-- statement:
--   The Fpy construction uses the sum Val mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sum.lean#L24-L43
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/FormatInference/Sum.lean#L24-L43

import Definitions.Def_Fpy_FormatInference_Sound
import Definitions.Def_Fpy_Sum
import Definitions.Def_Fpy_FormatInference_Sum
set_option autoImplicit true
open Fpy
variable {decode : List (Label × Val) → Option RoundCtx} {Φ : Program (fpy decode)}
  {D : FormatDomain} {A : Analysis (fpy decode) D}

theorem Fpy.sumVal_mem (hA : A.Sound Φ) {κ : Option Val} {C : Val} {r : Num → Num}
    (hκ : Admits κ C) (hr : C.rnd (fpy decode) = some r) {F : D.Fmt} :
    ∀ {us : List Num}, (∀ u ∈ us, u ∈ D.γ F) → sumVal r us ∈ D.γ (sumFmt A κ F us.length)
  := by sorry
