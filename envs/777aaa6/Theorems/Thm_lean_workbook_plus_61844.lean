-- Prove2me | Theorems.Thm_lean_workbook_plus_61844
-- name    : lean_workbook_plus_61844
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/25b8d5dd-c5c4-4177-94b2-a372ec4f5e14
-- statement:
--   If $a \equiv b \pmod{N}$ then $-a \equiv -b \pmod{N}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61844 : a ≡ b [ZMOD N] → -a ≡ -b [ZMOD N]   :=  by sorry
