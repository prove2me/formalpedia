-- Prove2me | Theorems.Thm_lean_workbook_plus_29299
-- name    : lean_workbook_plus_29299
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f4da2496-c675-452b-8184-bc38f1f5af6a
-- statement:
--   When n is a positive integer, $n!$ denotes the product of the first $n$ positive integers; that is, $n! = 1 \cdot 2 \cdot 3 \cdot ... \cdot n$ . Given that $7! = 5040$ , compute $8! + 9! + 10!$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29299 (h₁ : 7! = 5040) : 8! + 9! + 10! = 4032000   :=  by sorry
