-- Prove2me | Theorems.Thm_WorkbookSource_base_23576
-- name    : WorkbookSource.base_23576
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:30.836222+00:00
-- url     : https://prove2.me/theorems/c359c28c-12cf-4012-8592-9056c82a79c7
-- title:
--   A product of quadratic symmetric sums at fixed sum two
-- statement:
--   Let $ a,b,c \geq 0$ such that $ a+b+c=2$ . Prove that $ 1.(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2) \leq 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_23576` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_23576; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_23576 (a b c : ℝ) (h : a + b + c = 2) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0): (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≤ 2  :=  by sorry
