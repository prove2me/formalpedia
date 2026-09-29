-- Prove2me | Theorems.Thm_lean_workbook_plus_14152
-- name    : lean_workbook_plus_14152
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/78070655-993a-4bb8-86b2-ab76471f93b7
-- statement:
--   There is a nice proof for this inequality.\n\n$\dfrac{a^2}{a^2 +2bc} + \dfrac{b^2}{b^2+2ca} + \dfrac{c^2}{c^2+2ab} \geq \dfrac{(a+b+c)^2}{3(ab+bc+ca)}<=>$\n\n$\dfrac{3a^2(ab+bc+ca)}{a^2 +2bc} + \dfrac{3b^2(ab+bc+ca)}{b^2+2ca} + \dfrac{3c^2(ab+bc+ca)}{c^2+2ab} \geq (a+b+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14152 : ∀ a b c : ℝ, (a^2 / (a^2 + 2 * b * c) + b^2 / (b^2 + 2 * c * a) + c^2 / (c^2 + 2 * a * b) ≥ (a + b + c) ^ 2 / (3 * (a * b + b * c + a * c)))   :=  by sorry
