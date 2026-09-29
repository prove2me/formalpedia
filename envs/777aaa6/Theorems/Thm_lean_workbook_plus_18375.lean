-- Prove2me | Theorems.Thm_lean_workbook_plus_18375
-- name    : lean_workbook_plus_18375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8127c408-e98f-47a8-b22f-12561bde8414
-- statement:
--   Given the identity $(a+b+c+d)^2 - 2(a(b+c)+b(c+d)+c(d+a)+d(a+b)) = (b-d)^2 + (a-c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18375 : ∀ a b c d : ℤ, (a+b+c+d)^2 - 2 * (a * (b + c) + b * (c + d) + c * (d + a) + d * (a + b)) = (b - d)^2 + (a - c)^2   :=  by sorry
