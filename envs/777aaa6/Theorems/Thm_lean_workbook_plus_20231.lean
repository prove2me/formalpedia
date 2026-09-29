-- Prove2me | Theorems.Thm_lean_workbook_plus_20231
-- name    : lean_workbook_plus_20231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5c557228-f03a-4674-9599-fe99c1d2bdc4
-- statement:
--   Prove that if $p \equiv 0 \pmod 3$, the only such prime is $3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20231 (p : ℕ) (hp : p.Prime) (h : p ≡ 0 [ZMOD 3]) : p = 3   :=  by sorry
