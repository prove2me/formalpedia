-- Prove2me | Theorems.Thm_lean_workbook_plus_28097
-- name    : lean_workbook_plus_28097
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/210e3b13-14e9-4ea6-a1b4-fd2b11c92257
-- statement:
--   By Euler's Theorem, $2013^{\phi(343)}\equiv 2013^{294}\equiv 1\pmod{343}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28097 : 2013 ^ (294 : ℕ) ≡ 1 [ZMOD 343]   :=  by sorry
