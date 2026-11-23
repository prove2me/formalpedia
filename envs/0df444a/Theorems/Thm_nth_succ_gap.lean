-- Prove2me | Theorems.Thm_nth_succ_gap
-- name    : nth_succ_gap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T04:18:42.690742+00:00
-- url     : https://prove2.me/theorems/1adb9ec5-36a3-490f-8833-90f4d72d0d41
-- title:
--   nth succ gap: nth succ gap
-- statement:
--   The nth succ gap construction uses the nth succ gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L40-L47
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L40-L47

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
open Classical
variable {φ : ℕ → ℕ}

theorem nth_succ_gap {p : ℕ → Prop} (hf : (setOf p).Infinite) (n : ℕ) :
    ∀ k < Nat.nth p (n + 1) - Nat.nth p n, k > 0 → ¬ p (k + Nat.nth p n) := by sorry
