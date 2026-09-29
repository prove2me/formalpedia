-- Prove2me | Theorems.Thm_lean_workbook_plus_47079
-- name    : lean_workbook_plus_47079
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ae2f2113-21d3-4386-864d-16cbc2644b9d
-- statement:
--   From $ 10x + a = 2(a 10^k + x)$, deduce that $ 8x = a (2 \cdot 10^k - 1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47079 (x a k : ℕ) : 10 * x + a = 2 * (a * 10 ^ k + x) → 8 * x = a * (2 * 10 ^ k - 1)   :=  by sorry
