-- Prove2me | Theorems.Thm_lean_workbook_plus_19037
-- name    : lean_workbook_plus_19037
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/24f5596d-7ca2-4fd4-bd69-d57a382e3360
-- statement:
--   Prove $(2n + 1)^2 - 1 \equiv 0 \pmod 8$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19037 {n : ℤ} : (2 * n + 1) ^ 2 - 1 ≡ 0 [ZMOD 8]   :=  by sorry
