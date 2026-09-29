-- Prove2me | Theorems.Thm_lean_workbook_plus_20860
-- name    : lean_workbook_plus_20860
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/77c4d701-833f-4bfc-a8f1-66094c61fd5c
-- statement:
--   Find $7^{130} \pmod{11}$ using $7^5 \equiv -1 \pmod{11}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20860 (h₁ : 7^5 ≡ -1 [ZMOD 11]) : 7^130 ≡ 1 [ZMOD 11]   :=  by sorry
