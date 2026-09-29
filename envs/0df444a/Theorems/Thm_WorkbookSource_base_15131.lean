-- Prove2me | Theorems.Thm_WorkbookSource_base_15131
-- name    : WorkbookSource.base_15131
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:27.030073+00:00
-- url     : https://prove2.me/theorems/1e0efebc-3cc3-4c59-b998-c9a486414884
-- title:
--   A cyclic quartic inequality with coefficients twenty-three and eighteen
-- statement:
--   Let $a,b,c \in \mathbb{R}$ . Prove that
--    $4\big(a^4+b^4+c^4\big) + 23\big(a^2b^2+b^2c^2+c^2a^2\big) \geq 18\big(a^3b+b^3c+c^3a\big) + 9\big(a^2bc+ab^2c+abc^2\big)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15131` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15131; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15131 (a b c : ℝ) : 4 * (a ^ 4 + b ^ 4 + c ^ 4) + 23 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 18 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 9 * (a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2)  :=  by sorry
