-- Prove2me | Theorems.Thm_lean_workbook_plus_47996
-- name    : lean_workbook_plus_47996
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/05622c5b-3fc5-4bd8-8109-b2ba6741d83f
-- statement:
--   Prove that $a^n \equiv (a')^n \mod m$ if $a \equiv a' \mod m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47996 : ∀ {a a' m : ℕ}, a ≡ a' [ZMOD m] → ∀ n : ℕ, a ^ n ≡ a' ^ n [ZMOD m]   :=  by sorry
