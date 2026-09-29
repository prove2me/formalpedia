-- Prove2me | Theorems.Thm_lean_workbook_plus_80508
-- name    : lean_workbook_plus_80508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/49575886-8dcc-4a95-8bf8-845256cb0c1a
-- statement:
--   Prove that $(a^3k^4+a^3+3ak^4c^2+6ak^2c^2+8akc^2+b^3k^4-b^2c-b^2a-2k^2a^3+6k^2ca^2-8kca^2+6b^2ck^2-ba^2-bc^2-2b^3k^2-21bk^4ca+3bk^4c^2+3bk^4a^2+3bac-30bk^2ca+3b^2ak^4+8b^2kc+6b^2ak^2-8b^2ka-8bkc^2+6bk^2c^2+3b^2k^4c+6bk^2a^2+8bka^2+b^3+c^3-ac^2-a^2c+c^3k^4-2k^2c^3+3k^4ca^2)^2\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80508 (a b c k : ℝ) : (a^3 * k^4 + a^3 + 3 * a * k^4 * c^2 + 6 * a * k^2 * c^2 + 8 * a * k * c^2 + b^3 * k^4 - b^2 * c - b^2 * a - 2 * k^2 * a^3 + 6 * k^2 * c * a^2 - 8 * k * c * a^2 + 6 * b^2 * c * k^2 - b * a^2 - b * c^2 - 2 * b^3 * k^2 - 21 * b * k^4 * c + 3 * b * k^4 * c^2 + 3 * b * k^4 * a^2 + b * a * c - 30 * b * k^2 * c * a + 3 * b^2 * a * k^4 + 8 * b^2 * k * c + 6 * b^2 * a * k^2 - 8 * b^2 * k * a - 8 * b * k * c^2 + 6 * b * k^2 * c^2 + 3 * b^2 * k^4 * c + 6 * b * k^2 * a^2 + 8 * b * k * a^2 + b^3 + c^3 - a * c^2 - a^2 * c + c^3 * k^4 - 2 * k^2 * c^3 + 3 * k^4 * c * a^2)^2 ≥ 0   :=  by sorry
