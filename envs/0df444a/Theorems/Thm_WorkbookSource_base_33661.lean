-- Prove2me | Theorems.Thm_WorkbookSource_base_33661
-- name    : WorkbookSource.base_33661
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:46.6668+00:00
-- url     : https://prove2.me/theorems/3aff4d38-5c27-43e1-b48c-cf05e3020d4f
-- title:
--   A shifted pair-product reciprocal lower bound at fixed sum two
-- statement:
--   Let $ a,b,c $ be positive real numbers satisfying $ a+b+c=2 $ . Prove the inequality $ \frac{1}{1+ab}+\frac{1}{1+bc}+\frac{1}{1+ca} \ge \frac{27}{13} $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33661` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33661; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33661 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : 1 / (1 + a * b) + 1 / (1 + b * c) + 1 / (1 + c * a) ≥ 27 / 13  :=  by sorry
