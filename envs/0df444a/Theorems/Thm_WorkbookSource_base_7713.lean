-- Prove2me | Theorems.Thm_WorkbookSource_base_7713
-- name    : WorkbookSource.base_7713
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:04.708662+00:00
-- url     : https://prove2.me/theorems/1aa8d2ce-87ce-4453-ad04-3ee2f2d71a7a
-- title:
--   A mixed product bound with two moment constraints
-- statement:
--   Let $ a,b,c,d $ be reals such that $ a+b+c+d=4 $ and $a^2+b^2+c^2+d^2=18.$ Prove that $ ab-2cd \leq \frac{74}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7713` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7713; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7713 (a b c d : ℝ) (h₁ : a + b + c + d = 4) (h₂ : a^2 + b^2 + c^2 + d^2 = 18) : a * b - 2 * c * d ≤ 74 / 5  :=  by sorry
