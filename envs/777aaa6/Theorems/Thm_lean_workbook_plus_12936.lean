-- Prove2me | Theorems.Thm_lean_workbook_plus_12936
-- name    : lean_workbook_plus_12936
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/cb5ba78b-4758-4924-bded-2ad61eb21903
-- statement:
--   Prove that $2^{\phi (77)} \equiv 2^{60} \equiv 1 \ (\text{mod } 77)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12936 : 2 ^ (Nat.totient 77) ≡ 1 [ZMOD 77]   :=  by sorry
