-- Prove2me | Theorems.Thm_lean_workbook_plus_70186
-- name    : lean_workbook_plus_70186
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/918dccbf-f9c5-4cc2-b508-f53bc130f8e9
-- statement:
--   Given that $a$ and $b$ are multiples of $n$, prove or disprove that $a + b$ is also a multiple of $n$. Assume $n$, $a$, and $b$ are integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70186 (n a b : ℤ) (h1 : n ∣ a) (h2 : n ∣ b) : n ∣ a + b   :=  by sorry
