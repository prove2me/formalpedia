-- Prove2me | Theorems.Thm_WorkbookSource_problem_44189
-- name    : WorkbookSource.problem_44189
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:44.638605+00:00
-- url     : https://prove2.me/theorems/145ed875-b375-4aad-b344-fe6ec7f31fe5
-- title:
--   Factoring a cubic inequality
-- statement:
--   So we need to prove that:
--    $ p^3-8p^2+15p \le 0 \Leftrightarrow p(p-3)(p-5) \le 0$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_44189; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44189; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_44189 (p : ℝ) : p^3 - 8 * p^2 + 15 * p ≤ 0 ↔ p * (p - 3) * (p - 5) ≤ 0  :=  by sorry
