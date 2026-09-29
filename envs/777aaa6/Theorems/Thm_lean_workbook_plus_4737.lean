-- Prove2me | Theorems.Thm_lean_workbook_plus_4737
-- name    : lean_workbook_plus_4737
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e5037580-63a7-46c5-9dcf-2ef2d7bcdc8d
-- statement:
--   $4=ab+bc+ac+abc\geq3\sqrt[3]{(abc)^2}+abc\implies abc\leq 1 .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4737 : 4 = a * b + b * c + a * c + a * b * c ∧ a * b * c ≥ 3 * (a * b * c)^(2/3) + a * b * c → a * b * c ≤ 1   :=  by sorry
