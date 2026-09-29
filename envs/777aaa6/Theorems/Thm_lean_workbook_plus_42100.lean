-- Prove2me | Theorems.Thm_lean_workbook_plus_42100
-- name    : lean_workbook_plus_42100
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/4f5c75ef-05fd-42bc-bfc2-34f22ba281d7
-- statement:
--   Prove that $n^5\equiv n\mod 10$ for all positive integers n. In other words, prove that $n^5$ has the same units digit as $n$ for all positive integers n.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42100 (n : ℕ) (hn : 0 < n) : n^5 ≡ n [ZMOD 10]   :=  by sorry
