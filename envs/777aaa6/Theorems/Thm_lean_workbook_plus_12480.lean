-- Prove2me | Theorems.Thm_lean_workbook_plus_12480
-- name    : lean_workbook_plus_12480
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/16a4daaf-603f-48c8-810b-618c79373176
-- statement:
--   A number is divisible by 5 if and only if it ends in $ 5$ or $ 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12480 : ∀ n : ℕ, n % 10 = 5 ∨ n % 10 = 0 ↔ 5 ∣ n   :=  by sorry
