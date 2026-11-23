-- Prove2me | Theorems.Thm_odd_oddPart
-- name    : odd_oddPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:10:38.965289+00:00
-- url     : https://prove2.me/theorems/b3dc6094-65cf-41c5-a0ea-dfc56357a5e7
-- title:
--   odd odd Part: odd odd Part
-- statement:
--   The odd odd Part construction uses the odd odd Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L31-L37
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L31-L37

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}

theorem odd_oddPart [hn : NeZero n] : Odd (oddPart n) := by sorry
