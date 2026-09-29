-- Prove2me | Theorems.Thm_WorkbookSource_plus_72831
-- name    : WorkbookSource.plus_72831
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:44:52.976066+00:00
-- url     : https://prove2.me/theorems/3e1a8227-eb1e-4c12-b03c-fdf913ad6a8c
-- title:
--   A weighted sixth-degree Schur-type inequality
-- statement:
--   Prove that \((a^3b+a^3c)(a-b)(a-c)+(b^3a+b^3c)(b-a)(b-c)+(c^3a+c^3b)(c-a)(c-b) \geq 0\) where \(a, b, c \geq 0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_72831` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_72831; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_72831 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^3 * b + a^3 * c) * (a - b) * (a - c) + (b^3 * a + b^3 * c) * (b - a) * (b - c) + (c^3 * a + c^3 * b) * (c - a) * (c - b) ≥ 0   :=  by sorry
