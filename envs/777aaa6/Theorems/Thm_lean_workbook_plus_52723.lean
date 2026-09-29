-- Prove2me | Theorems.Thm_lean_workbook_plus_52723
-- name    : lean_workbook_plus_52723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3376c9f7-ce60-481c-aa98-68ecd5616815
-- statement:
--   Prove $(a^{2}+b^{2}+c^{2}+d^{2})^{2}\geq 16abcd$ by AM-GM.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52723 {a b c d : ℝ} : (a^2 + b^2 + c^2 + d^2)^2 ≥ 16 * a * b * c * d   :=  by sorry
