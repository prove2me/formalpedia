-- Prove2me | Theorems.Thm_lean_workbook_plus_61012
-- name    : lean_workbook_plus_61012
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/855c7fa4-128e-44ce-9e07-b5366283f2f6
-- statement:
--   Prove $4^n \equiv 1 \pmod{3}$ for all $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61012 (n:ℕ) : 4 ^ n ≡ 1 [ZMOD 3]   :=  by sorry
