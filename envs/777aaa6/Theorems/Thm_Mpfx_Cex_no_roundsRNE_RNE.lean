-- Prove2me | Theorems.Thm_Mpfx_Cex_no_roundsRNE_RNE
-- name    : Mpfx.Cex.no_roundsRNE_RNE
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-21T05:59:23.213924+00:00
-- url     : https://prove2.me/theorems/94e3948f-8868-4f9a-b2f5-4f51c4ebdb55
-- title:
--   Cex: no rounds RNE RNE
-- statement:
--   **RNE → RNE.** One extra digit makes the midpoint `m` of adjacent values
--   `u < u'` representable in `F₂`, and one of `u`, `u'` is even. The witness
--   `x = m ± δ` sits on the side of the other one: the intermediate RNE lands
--   exactly on `m`, a tie that breaks to the even value, while the direct RNE
--   returns the strictly nearer other one. (Tight: with `F₂ = F₁`,
--   RNE ∘ RNE = RNE by idempotence.)
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L393-L447
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Mpfx/DoubleRounding/Counterexample.lean#L393-L447

import Definitions.Def_Mpfx_DoubleRounding_Counterexample_Basic
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_DoubleRounding_Counterexample
set_option autoImplicit true
open Mpfx
open Mpfx.Cex

theorem Mpfx.Cex.no_roundsRNE_RNE (F₁ : ParityFormat) (h₁ : F₁.toFormat.HasPositive 1)
    (F₂ : FiniteFormat) (hsub : (F₁.toFiniteFormat.extend 1).toFormat ⊆ F₂.toFormat) :
    Disagrees F₂ (.nearest .toEven) F₁.toFiniteFormat (.nearest .toEven) := by sorry
