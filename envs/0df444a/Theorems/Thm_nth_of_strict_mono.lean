-- Prove2me | Theorems.Thm_nth_of_strict_mono
-- name    : nth_of_strict_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:13:27.122836+00:00
-- url     : https://prove2.me/theorems/f1ea2f6f-4383-4fd5-884f-f54f274eaedf
-- title:
--   nth of strict mono: nth of strict mono
-- statement:
--   The nth of strict mono construction uses the nth of strict mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L50-L56
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L50-L56

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem nth_of_strict_mono (hm : StrictMono φ) (n : ℕ) :
    φ n = Nat.nth (· ∈ range φ) n := by sorry
