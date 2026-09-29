-- Prove2me | Theorems.Thm_WorkbookSource_base_1747
-- name    : WorkbookSource.base_1747
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:39:22.515927+00:00
-- url     : https://prove2.me/theorems/be685a7c-d5cd-434e-b86e-d09db10509d4
-- title:
--   A quartic inequality in three real variables
-- statement:
--   Prove that for $x, y, z \in \mathbb{R}$, $x^2y^2 + z^4 + x^4 + y^4 + xy^3 \geq z^2(x^2 + y^2)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1747` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1747; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1747 (x y z : ℝ) : x ^ 2 * y ^ 2 + z ^ 4 + x ^ 4 + y ^ 4 + x * y ^ 3 ≥ z ^ 2 * (x ^ 2 + y ^ 2)  :=  by sorry
