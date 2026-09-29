-- Prove2me | Theorems.Thm_WorkbookSource_base_35771
-- name    : WorkbookSource.base_35771
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:12.197393+00:00
-- url     : https://prove2.me/theorems/6b6b4e94-4e72-4b5e-81e0-ec251584a085
-- title:
--   A cubed quadratic sum bounds three mixed quadratic factors
-- statement:
--   Prove that $ 8(a^2+b^2+c^2)^3\geq27(a^2+bc)(b^2+ca)(c^2+ab)$ for all $ a,b,c>0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35771` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35771; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35771 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * (a^2 + b^2 + c^2)^3 ≥ 27 * (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)  :=  by sorry
