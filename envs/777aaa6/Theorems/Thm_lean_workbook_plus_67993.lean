-- Prove2me | Theorems.Thm_lean_workbook_plus_67993
-- name    : lean_workbook_plus_67993
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/162b9b9b-fe67-475a-ada1-c635ce46f096
-- statement:
--   $x \equiv 1 \mod 4 \implies x^2 \equiv 1 \mod 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67993 {x : ℤ} (h : x ≡ 1 [ZMOD 4]) : x^2 ≡ 1 [ZMOD 4]   :=  by sorry
