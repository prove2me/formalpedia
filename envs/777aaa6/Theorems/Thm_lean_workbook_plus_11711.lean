-- Prove2me | Theorems.Thm_lean_workbook_plus_11711
-- name    : lean_workbook_plus_11711
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/0f2b6304-d124-4809-bbe5-892da2990fae
-- statement:
--   Prove the identity $4(a^2+b^2+c^2-ab-bc-ca)[(a^2+b^2+c^2)^2-3(a^3b+b^3c+c^3a)] = [(a^3+b^3+c^3)-5(a^2b+b^2c+c^2a)+4(ab^2+bc^2+ca^2)]^2 + 3[(a^3+b^3+c^3)-(a^2b+b^2c+c^2a)-2(ab^2+bc^2+ca^2)+6abc]^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11711 b c : ℝ) : 4 * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) * ((a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 3 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a)) = (a ^ 3 + b ^ 3 + c ^ 3 - 5 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) + 4 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2)) ^ 2 + 3 * (a ^ 3 + b ^ 3 + c ^ 3 - a ^ 2 * b - b ^ 2 * c - c ^ 2 * a - 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 6 * a * b * c) ^ 2   :=  by sorry
