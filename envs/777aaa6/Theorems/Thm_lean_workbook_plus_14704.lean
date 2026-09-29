-- Prove2me | Theorems.Thm_lean_workbook_plus_14704
-- name    : lean_workbook_plus_14704
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/caa42968-43d9-46be-b2ce-c346fe991225
-- statement:
--   $a+d-b-c\equiv0\pmod {p^k}\implies a\equiv b+c-d\equiv0\pmod {p^k}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14704 : ∀ {a b c d : ℤ} {p : ℕ} {k : ℕ},
  a + d - b - c ≡ 0 [ZMOD p ^ k] → a ≡ b + c - d [ZMOD p ^ k]   :=  by sorry
