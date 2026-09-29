-- Prove2me | Theorems.Thm_lean_workbook_plus_27394
-- name    : lean_workbook_plus_27394
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/603e54c7-9123-4000-b0ea-451704476acb
-- statement:
--   $ (a^{2}+b^{2})(c^{2}+d^{2}) = (ad-bc)^{2}+(ac+bd)^{2} $ is an identity (that is, it holds for all values of $a$ , $b$ , $c$ , $d$ . In fact, it is a special (two-variable) case of Lagrange's Identity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27394 {a b c d : ℂ} : (a^2 + b^2) * (c^2 + d^2) = (a * d - b * c)^2 + (a * c + b * d)^2   :=  by sorry
