-- Prove2me | Theorems.Thm_lean_workbook_plus_35795
-- name    : lean_workbook_plus_35795
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/a3ed2dd1-ecc2-4d6c-8160-0a5594119c42
-- statement:
--   In triangle, $a,b,c \in \mathbb N$ , prove that $a+b^2 \ge b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35795 (a b c : ℕ) (hx: a + b + c = 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a + b^2 >= b + c   :=  by sorry
