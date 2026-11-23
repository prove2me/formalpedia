-- Prove2me | Theorems.Thm_oddPart_of_odd
-- name    : oddPart_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:45.490975+00:00
-- url     : https://prove2.me/theorems/d2183798-ce8d-4934-9818-8cc21fd5853f
-- title:
--   odd Part of odd: odd Part of odd
-- statement:
--   The odd Part of odd construction uses the odd Part of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L41-L42
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L41-L42

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}

theorem oddPart_of_odd (ho : Odd n) : oddPart n = n := by sorry
