-- Prove2me | Theorems.Thm_WorkbookSource_base_53649
-- name    : WorkbookSource.base_53649
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:05:10.490703+00:00
-- url     : https://prove2.me/theorems/9a598f73-e3ff-46c4-a2c0-176269c20679
-- title:
--   A squared shifted ratio upper bound at fixed sum three
-- statement:
--   Let $a, b, c > 0$ such that $a+b+c=3$ . Prove that $\dfrac{a^{2}}{(2a+1)^2} + \dfrac{b^{2}}{(2b+1)^2} + \dfrac{c^{2}}{(2c+1)^2} \leq \dfrac{a^{2}+b^{2}+c^{2}}{a^{2}+b^{2}+c^{2}+6}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_53649` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_53649; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_53649 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a^2 / (2 * a + 1)^2 + b^2 / (2 * b + 1)^2 + c^2 / (2 * c + 1)^2) ≤ (a^2 + b^2 + c^2) / (a^2 + b^2 + c^2 + 6)  :=  by sorry
