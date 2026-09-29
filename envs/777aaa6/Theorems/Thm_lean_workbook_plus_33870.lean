-- Prove2me | Theorems.Thm_lean_workbook_plus_33870
-- name    : lean_workbook_plus_33870
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/e28394bb-9fb6-49ad-89f0-fdc141096097
-- statement:
--   Prove that $ \text{odd}\times\text{odd}=\text{odd}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33870 {m n : ℤ} (hm : m % 2 = 1) (hn : n % 2 = 1) : (m * n) % 2 = 1   :=  by sorry
