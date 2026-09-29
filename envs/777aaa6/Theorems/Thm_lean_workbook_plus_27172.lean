-- Prove2me | Theorems.Thm_lean_workbook_plus_27172
-- name    : lean_workbook_plus_27172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/717d5d92-a807-40fa-9b05-2967a150f436
-- statement:
--   Find the sum of the coefficients of the expansion of $(\sqrt{a}+2\sqrt[3]{b}+3\sqrt[5]{c})^{2018}$ when $a=b=c=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27172 (a b c : ℝ) (ha : a = 1) (hb : b = 1) (hc : c = 1) : (a^(1/2) + 2 * b^(1/3) + 3 * c^(1/5))^2018 = 6^2018   :=  by sorry
