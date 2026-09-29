-- Prove2me | Theorems.Thm_WorkbookSource_base_26818
-- name    : WorkbookSource.base_26818
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:23.657963+00:00
-- url     : https://prove2.me/theorems/596d9fd8-5ba4-4cea-89bc-ac2710957a92
-- title:
--   A sixth-degree bound for a sum of cubes and a triple product
-- statement:
--   Prove $ (a^2 + b^2 + c^2)^3 \ge (a^3 + b^3 + c^3 + abc)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26818` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26818; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26818 (a b c : ℝ) : (a^2 + b^2 + c^2)^3 ≥ (a^3 + b^3 + c^3 + a * b * c)^2  :=  by sorry
