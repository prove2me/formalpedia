-- Prove2me | Theorems.Thm_Fpy_DigitBound_Covers_fmt
-- name    : Fpy.DigitBound.Covers.fmt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:26:24.105137+00:00
-- url     : https://prove2.me/theorems/b6e219f1-f628-4625-8375-4405a198b351
-- title:
--   Covers: fmt
-- statement:
--   D-Fmt for a loop variable: a number in the format `F`, whose values have
--   digits in `[lo, hi]`, gets a fresh interval.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L72-L88
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/DigitBound/Join.lean#L72-L88

import Definitions.Def_Fpy_DigitBound_Basic
import Definitions.Def_Fpy_DigitBound_Join
set_option autoImplicit true
open Fpy Fpy.DigitBound

theorem Fpy.DigitBound.Covers.fmt {D : FormatDomain} {Ψg Ψ : List Con} {n₀ n₁ : ℕ} {X : List Var}
    {Γᵢ : AEnv D} {Δ Δᵢ : DEnv} {x : Var} {F : D.Fmt} {lo hi : EInt}
    (h : Covers n₀ n₁ Ψg Ψ X Γᵢ Δ Δᵢ) (hF : Fresh n₀ n₁ Ψ) (hΔᵢ : Δᵢ.Below n₁)
    (hx : Γᵢ x = some (.fmt F)) (hin : ∀ w ∈ D.γ F, InRange lo hi w) :
    Covers n₀ (n₁ + 2) Ψg (Ψ ++ bounds n₁ (.const lo) (.const hi) trivial trivial) X Γᵢ Δ
      (Δᵢ.update x (.num (.var (n₁ + 1)) (.var n₁) none)) := by sorry
