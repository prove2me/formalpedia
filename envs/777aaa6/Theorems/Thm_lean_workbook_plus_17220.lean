-- Prove2me | Theorems.Thm_lean_workbook_plus_17220
-- name    : lean_workbook_plus_17220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1e93653f-0691-4a9b-932d-59e619ead68e
-- statement:
--   prove that: $ a(c-d)(ac-b^2-ad+cd)+b(d-a)(ad-c^2-ab+bd)+c(a-b)(ab-d^2-bc+ac)+d(b-c)(bc-a^2-cd+bd) = 1/4(ab-ad-bc+ac-bd+cd)^2+1/8(b-d)^2(a-c)^2+3/4(bd-ac)^2+3/4(ac-bd)^2+1/4(ad-ab-ac+bc-cd+bd)^2+1/8(-a+c)^2(b-d)^2+1/8(-b+d)^2(-a+c)^2+1/8(a-c)^2(-b+d)^2, $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17220 (a b c d : ℝ) :
  a * (c - d) * (a * c - b ^ 2 - a * d + c * d) + b * (d - a) * (a * d - c ^ 2 - a * b + b * d) + c * (a - b) * (a * b - d ^ 2 - b * c + c * a) + d * (b - c) * (b * c - a ^ 2 - c * d + d * b) =
  1 / 4 * (a * b - a * d - b * c + c * a - b * d + d * c) ^ 2 + 1 / 8 * (b - d) ^ 2 * (a - c) ^ 2 + 3 / 4 * (b * d - a * c) ^ 2 + 3 / 4 * (a * c - b * d) ^ 2 + 1 / 4 * (a * d - a * b - a * c + b * c - c * d + b * d) ^ 2 + 1 / 8 * (-a + c) ^ 2 * (b - d) ^ 2 + 1 / 8 * (-b + d) ^ 2 * (-a + c) ^ 2 + 1 / 8 * (a - c) ^ 2 * (-b + d) ^ 2   :=  by sorry
