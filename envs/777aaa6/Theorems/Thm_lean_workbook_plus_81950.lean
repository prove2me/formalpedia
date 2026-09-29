-- Prove2me | Theorems.Thm_lean_workbook_plus_81950
-- name    : lean_workbook_plus_81950
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/394d4efb-b24c-46d5-b51b-31637c1390c9
-- statement:
--   take hypothetical two number $e,f$ \n$f=5^2$ $e=7^4$ \n$e>f$ but $e\nmid{f}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81950 : ∃ e f : ℕ, f = 5^2 ∧ e = 7^4 ∧ e > f ∧ ¬ e ∣ f   :=  by sorry
