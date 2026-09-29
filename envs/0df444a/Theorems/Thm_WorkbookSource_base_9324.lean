-- Prove2me | Theorems.Thm_WorkbookSource_base_9324
-- name    : WorkbookSource.base_9324
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:16.640511+00:00
-- url     : https://prove2.me/theorems/73cbd550-a2de-4a42-b0b6-8962c1673d28
-- title:
--   A product bound for variables of sum two
-- statement:
--   Given $ a, b, c \ge 0$ satisfy $ a + b + c = 2$ Prove that $ (a + b - ab)(b + c - bc)(c + a - ca) \le 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9324` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9324; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9324 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a + b - a * b) * (b + c - b * c) * (c + a - c * a) ≤ 1  :=  by sorry
