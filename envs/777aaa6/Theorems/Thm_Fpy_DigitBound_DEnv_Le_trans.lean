-- Prove2me | Theorems.Thm_Fpy_DigitBound_DEnv_Le_trans
-- name    : Fpy.DigitBound.DEnv.Le.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:23:21.376149+00:00
-- url     : https://prove2.me/theorems/ff790ca2-57bc-42e0-8479-5e03291c1b25
-- title:
--   Le: trans
-- statement:
--   The Le construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L51-L60
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L51-L60

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.DEnv.Le.trans {Ψg Ψ₁ Ψ₂ : List Con} {n₀ n₁ n₂ : ℕ} {Δ Δ₁ Δ₂ : DEnv}
    (h₁ : DEnv.Le n₀ n₁ Ψg Ψ₁ Δ Δ₁) (h₂ : DEnv.Le n₁ n₂ (Ψg ++ Ψ₁) Ψ₂ Δ₁ Δ₂)
    (hF₁ : Fresh n₀ n₁ Ψ₁) (hF₂ : Fresh n₁ n₂ Ψ₂) :
    DEnv.Le n₀ n₂ Ψg (Ψ₁ ++ Ψ₂) Δ Δ₂ := by sorry
