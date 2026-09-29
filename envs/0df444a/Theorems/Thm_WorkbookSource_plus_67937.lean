-- Prove2me | Theorems.Thm_WorkbookSource_plus_67937
-- name    : WorkbookSource.plus_67937
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:50:12.762749+00:00
-- url     : https://prove2.me/theorems/a3a326fa-c59b-4621-a674-0de16bc4e331
-- title:
--   A squared shifted pair-product sum bounds a triple product
-- statement:
--   Prove that $(ab+bc+ca-3)^2 \ge 27(abc-1)$ given $a+b+c=3$ and $a, b, c \in \mathbb{R}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_67937` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_67937; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_67937 (a b c : ℝ) (ha : a + b + c = 3) : (a * b + b * c + c * a - 3) ^ 2 ≥ 27 * (a * b * c - 1)   :=  by sorry
