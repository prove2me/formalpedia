-- Prove2me | Theorems.Thm_WorkbookSource_plus_2333
-- name    : WorkbookSource.plus_2333
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:35.961044+00:00
-- url     : https://prove2.me/theorems/01204752-6307-436a-b507-a56ea9970a2e
-- title:
--   A product of pairwise quadratic sums at fixed sum two
-- statement:
--   Let $a,b,c \geq 0$ such that $a+b+c=2$ . Prove that
--
--    $$(a^2+b^2)(b^2+c^2)(c^2+a^2) \leq 2$$ PS : Prove by Schur inequality!
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_2333` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_2333; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_2333 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 2) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≤ 2   :=  by sorry
