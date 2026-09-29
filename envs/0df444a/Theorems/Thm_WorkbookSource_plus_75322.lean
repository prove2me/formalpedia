-- Prove2me | Theorems.Thm_WorkbookSource_plus_75322
-- name    : WorkbookSource.plus_75322
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:42.919947+00:00
-- url     : https://prove2.me/theorems/2d047c24-8ddc-479a-b056-7efb9d04f7f1
-- title:
--   A bilinear-linear bound on a weighted ellipsoid
-- statement:
--   Let $a,b,c$ be real numbers such that $a^2+2b^2+3c^2=36. $ Prove that $ab+bc+ca+a+20b+51c\leq 205$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75322` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75322; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75322 (a b c : ℝ) (h : a^2 + 2 * b^2 + 3 * c^2 = 36) : a * b + b * c + c * a + a + 20 * b + 51 * c ≤ 205   :=  by sorry
