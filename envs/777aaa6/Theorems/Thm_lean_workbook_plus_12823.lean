-- Prove2me | Theorems.Thm_lean_workbook_plus_12823
-- name    : lean_workbook_plus_12823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3548b939-dea9-454f-9c6f-b64837386e68
-- statement:
--   Prove that for any integer $ x$ , $ x^2 \equiv 0\pmod{4}$ or $ x^2 \equiv 1\pmod{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12823 {x : ℤ} : x ^ 2 ≡ 0 [ZMOD 4] ∨ x ^ 2 ≡ 1 [ZMOD 4]   :=  by sorry
