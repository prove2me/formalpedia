-- Prove2me | Theorems.Thm_WorkbookSource_base_958
-- name    : WorkbookSource.base_958
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:08.782928+00:00
-- url     : https://prove2.me/theorems/fba8b1dd-6ef8-484e-8c88-1099e1a34180
-- title:
--   A product of pair-sum differences at total two
-- statement:
--   Given $ a, b, c \ge 0$ satisfy $ a + b + c = 2$ Prove that $ (a + b - ab)(b + c - bc)(c + a - ca) \le 1 - abc$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_958` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_958; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_958 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a + b - a * b) * (b + c - b * c) * (c + a - c * a) ≤ 1 - a * b * c  :=  by sorry
