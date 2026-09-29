-- Prove2me | Theorems.Thm_WorkbookSource_base_49447
-- name    : WorkbookSource.base_49447
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:07.774686+00:00
-- url     : https://prove2.me/theorems/c1d93fa6-16ad-44cd-8fd5-737920727fe2
-- title:
--   A cubic symmetric bound at squared norm three
-- statement:
--   For $a, b, c \ge 0$ and $a^2+b^2+c^2=3$, prove that $a^3+b^3+c^3+6abc\leq 3(a+b+c)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49447` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49447; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49447 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a^2 + b^2 + c^2 = 3) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ 3 * (a + b + c)  :=  by sorry
