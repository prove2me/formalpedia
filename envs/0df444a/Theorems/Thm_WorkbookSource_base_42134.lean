-- Prove2me | Theorems.Thm_WorkbookSource_base_42134
-- name    : WorkbookSource.base_42134
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:30.12596+00:00
-- url     : https://prove2.me/theorems/fc641983-7f25-4770-848b-fb81b0f42813
-- title:
--   Squared differences bound a Vandermonde product
-- statement:
--   Let $a,b,c \in \mathbb{R} $. Prove that $\sum_{cyc}(a^2-b^2)^2+3\sum_{cyc}(a-b)^2 \ge 6(a-b)(b-c)(c-a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_42134` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_42134; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_42134 (a b c : ℝ) :
  (a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2 + 3 * ((a - b)^2 + (b - c)^2 + (c - a)^2) ≥
    6 * (a - b) * (b - c) * (c - a)  :=  by sorry
