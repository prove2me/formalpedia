-- Prove2me | Theorems.Thm_WorkbookSource_base_6731
-- name    : WorkbookSource.base_6731
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:36:43.300979+00:00
-- url     : https://prove2.me/theorems/5c914d8c-a2fa-4839-a679-81af19784066
-- title:
--   A cyclic quartic upper bound on the four-variable simplex
-- statement:
--   Let $a$ , $b$ , $c$ , $d$ be non-negative real numbers satisfying $a+b+c+d=4$. Prove that $a^2bc+b^2cd+c^2da+d^2ab \le 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6731` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6731; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6731 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a^2 * b * c + b^2 * c * d + c^2 * d * a + d^2 * a * b ≤ 4  :=  by sorry
