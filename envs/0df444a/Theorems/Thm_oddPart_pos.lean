-- Prove2me | Theorems.Thm_oddPart_pos
-- name    : oddPart_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:11:59.486262+00:00
-- url     : https://prove2.me/theorems/ff06cd43-24be-46d0-84de-a0b9b4359849
-- title:
--   odd Part pos: odd Part pos
-- statement:
--   The odd Part pos construction uses the odd Part pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L39-L39
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L39-L39

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}

theorem oddPart_pos [NeZero n] : 0 < oddPart n := by sorry
