-- Prove2me | Theorems.Thm_WorkbookSource_plus_70753
-- name    : WorkbookSource.plus_70753
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:44:38.798676+00:00
-- url     : https://prove2.me/theorems/6244c829-aec0-4c30-b841-c35eff04d5ed
-- title:
--   A sum of mixed quadratic products at fixed sum two
-- statement:
--   Let $a,b,c$ be non-negative real numbers such that $a+b+c=2$. Prove that $(a^{2}+bc)(b^{2}+ca)+(b^{2}+ca)(c^{2}+ab)+(c^{2}+ab)(a^{2}+bc) \le 3.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_70753` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_70753; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_70753 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a^2 + b * c) * (b^2 + c * a) + (b^2 + c * a) * (c^2 + a * b) + (c^2 + a * b) * (a^2 + b * c) ≤ 3   :=  by sorry
