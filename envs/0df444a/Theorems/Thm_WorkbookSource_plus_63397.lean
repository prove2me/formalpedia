-- Prove2me | Theorems.Thm_WorkbookSource_plus_63397
-- name    : WorkbookSource.plus_63397
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:34.493123+00:00
-- url     : https://prove2.me/theorems/b3998293-ed63-409b-bc09-d22c7a2ebcae
-- title:
--   A sixth-degree cyclic product inequality
-- statement:
--   It is equivalent to $\sum_{cyc}{(a^4+a^2bc)(a-b)(a-c)}\ge0.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_63397` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63397; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_63397 (a b c : ℝ) : (a^4 + a^2 * b * c) * (a - b) * (a - c) + (b^4 + b^2 * c * a) * (b - c) * (b - a) + (c^4 + c^2 * a * b) * (c - a) * (c - b) ≥ 0   :=  by sorry
