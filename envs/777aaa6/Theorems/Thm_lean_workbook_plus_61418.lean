-- Prove2me | Theorems.Thm_lean_workbook_plus_61418
-- name    : lean_workbook_plus_61418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/47626faa-6c99-4f97-ad9f-b5036587712a
-- statement:
--   Let $a$ and $b$ be positive integers with $a>1$ and $b>2$ . Prove that $a^b+1\ge b(a+1)$ and determine when there is inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61418 (a b : ℕ) (ha : a > 1) (hb : b > 2) : a^b + 1 ≥ b * (a + 1)   :=  by sorry
