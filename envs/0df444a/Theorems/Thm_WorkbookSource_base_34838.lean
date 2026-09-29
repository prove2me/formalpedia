-- Prove2me | Theorems.Thm_WorkbookSource_base_34838
-- name    : WorkbookSource.base_34838
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:31:45.852413+00:00
-- url     : https://prove2.me/theorems/8268da2e-c9a2-4583-8560-43cc98299e16
-- title:
--   An eighth-degree symmetric power sum bound with a mixed correction
-- statement:
--   Let $a,b,c \in R^+$ . Prove:
--
--    $$(a^2+b^2+c^2)^4 - a^8-b^8-c^8 \geq 14b^2c^2(b^2c^2+4a^4)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34838` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34838; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34838 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2)^4 - a^8 - b^8 - c^8 ≥ 14 * b^2 * c^2 * (b^2 * c^2 + 4 * a^4)  :=  by sorry
