-- Prove2me | Theorems.Thm_lean_workbook_plus_82317
-- name    : lean_workbook_plus_82317
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a857f2c2-103a-4734-b236-9f74e4d9a919
-- statement:
--   $x \equiv 2 \mod 4 \implies x^2 \equiv 0 \mod 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82317 {x : ℤ} (h : x ≡ 2 [ZMOD 4]) : x^2 ≡ 0 [ZMOD 4]   :=  by sorry
