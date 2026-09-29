-- Prove2me | Theorems.Thm_WorkbookSource_base_15779
-- name    : WorkbookSource.base_15779
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:31.11299+00:00
-- url     : https://prove2.me/theorems/504e37b4-ceb7-4890-93cc-d598b71e9076
-- title:
--   A linear-bilinear bound on a circle
-- statement:
--   Let $a,b>0$ and $ a^2+b^2=5.$ Prove that $$ ab+a+5b\leq 13$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15779` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15779; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15779 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 5) : a * b + a + 5 * b ≤ 13  :=  by sorry
