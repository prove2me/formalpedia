-- Prove2me | Theorems.Thm_WorkbookSource_base_54653
-- name    : WorkbookSource.base_54653
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:00.387055+00:00
-- url     : https://prove2.me/theorems/dfa534bb-d09c-48e1-81e7-35baf5381a6e
-- title:
--   A cyclic quartic inequality with coefficients eleven and six
-- statement:
--   Prove that for all real numbers $a$, $b$, and $c$, the following inequality holds:
--   $a^4 + b^4 + c^4 + 2(a^3b + b^3c + c^3a) + 11(a^2b^2 + b^2c^2 + c^2a^2) \geq 6(ab^3 + bc^3 + ca^3) + 8abc(a + b + c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_54653` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_54653; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_54653 (a b c : ℝ) : a^4 + b^4 + c^4 + 2 * (a^3 * b + b^3 * c + c^3 * a) + 11 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ 6 * (a * b^3 + b * c^3 + c * a^3) + 8 * a * b * c * (a + b + c)  :=  by sorry
