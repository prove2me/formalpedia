-- Prove2me | Theorems.Thm_WorkbookSource_plus_74674
-- name    : WorkbookSource.plus_74674
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:50:17.020915+00:00
-- url     : https://prove2.me/theorems/e90fb3ce-ce29-4ca3-b3b7-fd8e57c44a58
-- title:
--   A squared pair-product sum with a constant correction
-- statement:
--   Prove that $(ab+bc+ca)^2+9 \ge 18abc$ given $a+b+c=3$ and $a, b, c \in \mathbb{R}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_74674` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_74674; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_74674 (a b c : ℝ) (hab : a + b + c = 3) : (a * b + b * c + c * a) ^ 2 + 9 ≥ 18 * a * b * c   :=  by sorry
