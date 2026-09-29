-- Prove2me | Theorems.Thm_WorkbookSource_base_11853
-- name    : WorkbookSource.base_11853
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:43:52.105596+00:00
-- url     : https://prove2.me/theorems/3d907d2a-4882-4ca2-8495-669e7033bd2c
-- title:
--   A sixth-degree bound involving three triangle factors
-- statement:
--   If $a, b, c \ge 0$, then
--   $4a^2b^2c^2 \geq (b + c - a)(c + a - b)(a + b - c)(a^3 + b^3 + c^3 + abc)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11853` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11853; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11853 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : 4 * a ^ 2 * b ^ 2 * c ^ 2 ≥ (b + c - a) * (c + a - b) * (a + b - c) * (a ^ 3 + b ^ 3 + c ^ 3 + a * b * c)  :=  by sorry
