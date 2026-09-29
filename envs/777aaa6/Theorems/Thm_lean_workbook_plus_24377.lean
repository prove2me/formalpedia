-- Prove2me | Theorems.Thm_lean_workbook_plus_24377
-- name    : lean_workbook_plus_24377
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ff40a57d-4ab5-4ab5-b034-3af6f04081a8
-- statement:
--   $\mathbb{Z^*}$ or $\mathbb{Z}$ \ $\{0\}$ means excluding $0$ , right? (By the way, how do you LaTeX a \?)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24377 : { z : ℤ | z ≠ 0 } = { z : ℤ | z ∈ Set.univ \ {0} }   :=  by sorry
