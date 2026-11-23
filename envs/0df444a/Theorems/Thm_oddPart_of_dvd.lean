-- Prove2me | Theorems.Thm_oddPart_of_dvd
-- name    : oddPart_of_dvd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:13:48.125183+00:00
-- url     : https://prove2.me/theorems/03a68fd7-9088-4692-8806-926aa85956ab
-- title:
--   odd Part of dvd: odd Part of dvd
-- statement:
--   The odd Part of dvd construction uses the odd Part of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L49-L54
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/Val2.lean#L49-L54

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Definitions.Def_MillerRabin_Val2
set_option autoImplicit false
open Nat
variable {n : ℕ}
variable {m : ℕ}

theorem oddPart_of_dvd [NeZero m] (h : m ∣ n) : oddPart m ∣ oddPart n := by sorry
