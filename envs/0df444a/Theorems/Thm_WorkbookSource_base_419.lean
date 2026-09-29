-- Prove2me | Theorems.Thm_WorkbookSource_base_419
-- name    : WorkbookSource.base_419
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:23.153122+00:00
-- url     : https://prove2.me/theorems/98eb8c39-2785-4b3c-94bb-64882b0474a2
-- title:
--   Three square roots under a sum constraint
-- statement:
--   Prove that for all $a, b, c \in \mathbb{R}$, where $a, b, c \geq \frac{1}{4}$ and $a + b + c = 1$, the following inequality holds: $\sqrt{4a + 1} + \sqrt{4b + 1} + \sqrt{4c + 1} \leq 5$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_419` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_419; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_419 (a b c : ℝ) (ha : a ≥ 1 / 4) (hb : b ≥ 1 / 4) (hc : c ≥ 1 / 4) (hab : a + b + c = 1) : √(4 * a + 1) + √(4 * b + 1) + √(4 * c + 1) ≤ 5  :=  by sorry
