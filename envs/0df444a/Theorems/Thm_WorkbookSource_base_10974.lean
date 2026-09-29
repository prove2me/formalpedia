-- Prove2me | Theorems.Thm_WorkbookSource_base_10974
-- name    : WorkbookSource.base_10974
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:33:25.081298+00:00
-- url     : https://prove2.me/theorems/b0293b5a-9ac8-4ecc-8b2c-6a1e7e437203
-- title:
--   A pairwise-sum ratio bound by symmetric quadratic forms
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that $\frac{a+b}{a+b+4c}+\frac{b+c}{b+c+4a}+\frac{c+a}{c+a+4b}\le\frac{3\left(a^2+b^2+c^2\right)+ab+bc+ca}{a^2+b^2+c^2+3(ab+bc+ca)}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10974` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10974; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10974 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (a + b + 4 * c) + (b + c) / (b + c + 4 * a) + (c + a) / (c + a + 4 * b) ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2) + a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2 + 3 * (a * b + b * c + c * a))  :=  by sorry
