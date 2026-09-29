-- Prove2me | Theorems.Thm_lean_workbook_plus_73449
-- name    : lean_workbook_plus_73449
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/a63ffc99-5dc4-4230-9f40-cb64f8da7cc7
-- statement:
--   By wilson theorem $ (n-1)!\equiv-1(modn) \implies (n-2)!\equiv1(modn) $ . so n leaves remainder 1 when divide (n-2)! .Hence $n^2$ cannot divide (n-2)!.therefore there exists no such natural nos that $n^2|(n-2)!$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73449 : ¬ (∃ n : ℕ, n^2 ∣ (n-2)!)   :=  by sorry
