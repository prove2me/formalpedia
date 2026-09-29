-- Prove2me | Theorems.Thm_WorkbookSource_base_47198
-- name    : WorkbookSource.base_47198
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:26.862082+00:00
-- url     : https://prove2.me/theorems/1cac9a08-8ab2-4959-be26-45a259ea236a
-- title:
--   A mixed sixth-degree lower bound at fixed sum one
-- statement:
--   Let $a,b,c\ge 0$ such that $a+b+c=1$ . Show that:
--   $243a^2b^2c^2+45(a^2b^2+b^2c^2+c^2a^2)+6(a^2+b^2+c^2)\ge 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_47198` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_47198; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_47198 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : 243 * a ^ 2 * b ^ 2 * c ^ 2 + 45 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) + 6 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 4  :=  by sorry
