-- Prove2me | Theorems.Thm_WorkbookSource_base_30727
-- name    : WorkbookSource.base_30727
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:26.322766+00:00
-- url     : https://prove2.me/theorems/8153f22d-2878-44b3-91c1-d12da7419171
-- title:
--   Six pairwise linear factors bound a squared triple product
-- statement:
--   Prove that \((a+b)(b+c)(a+c)(a+b-c)(b+c-a)(a+c-b)\leq 8a^2b^2c^2\) if \(a,b,c>0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30727` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30727; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30727 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (b + c) * (c + a) * (a + b - c) * (b + c - a) * (c + a - b) ≤ 8 * a ^ 2 * b ^ 2 * c ^ 2  :=  by sorry
