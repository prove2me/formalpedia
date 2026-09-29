-- Prove2me | Theorems.Thm_lean_workbook_plus_73508
-- name    : lean_workbook_plus_73508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b159e4f4-b9e8-44ea-a300-8123bfab20b8
-- statement:
--   $2x\equiv 0 \mod 6$ implies $x\equiv 0 \mod 6$ or $x\equiv 3 \mod 6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73508 : ∀ x : ℤ, 2 * x ≡ 0 [ZMOD 6] → x ≡ 0 [ZMOD 6] ∨ x ≡ 3 [ZMOD 6]   :=  by sorry
