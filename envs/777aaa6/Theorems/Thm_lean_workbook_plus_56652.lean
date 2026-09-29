-- Prove2me | Theorems.Thm_lean_workbook_plus_56652
-- name    : lean_workbook_plus_56652
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e568bc8d-6425-48f8-8dff-5f51cd5f5393
-- statement:
--   Evaluate using $\pi=3.14:$ $\lceil \pi \rceil +\lfloor \pi \rfloor+ \lceil -\pi \rceil + \{ \pi \} + \{ -\pi \}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56652 (h : π = 3.14) : Int.ceil π + Int.floor π + Int.ceil (-π) + Int.fract π + Int.fract (-π) = 5   :=  by sorry
