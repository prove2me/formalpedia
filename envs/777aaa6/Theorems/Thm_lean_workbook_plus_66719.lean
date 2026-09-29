-- Prove2me | Theorems.Thm_lean_workbook_plus_66719
-- name    : lean_workbook_plus_66719
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/d9dbd077-0166-439d-b11c-fee7e755ec48
-- statement:
--   If $a \mid b$ and $c \mid d$ , then $ac \mid bd$ , right? Can you please explain more?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66719 (a b c d : ℕ) (hab : a ∣ b) (hcd : c ∣ d) : a*c ∣ b*d   :=  by sorry
