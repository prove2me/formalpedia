-- Prove2me | Theorems.Thm_lean_workbook_plus_13808
-- name    : lean_workbook_plus_13808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0ec51469-9662-4d35-9bc9-addee4c666a9
-- statement:
--   Prove or disprove: If $a \rightarrow b$ and $b\rightarrow c$, then $a\rightarrow c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13808 (a b c : Prop) (hab : a → b) (hbc : b → c) : a → c   :=  by sorry
