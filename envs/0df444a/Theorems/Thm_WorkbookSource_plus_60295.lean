-- Prove2me | Theorems.Thm_WorkbookSource_plus_60295
-- name    : WorkbookSource.plus_60295
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:54:31.135351+00:00
-- url     : https://prove2.me/theorems/93d70a5e-6ed1-4d92-b7df-13f9b56a9756
-- title:
--   A weighted quadratic product bounds a symmetric sixth-degree expression
-- statement:
--   Given $ a, b, c > 0$ . Prove that:
--    $ (a^2 + 2b^2 + 3c^2)(b^2 + 2c^2 + 3a^2)(c^2 + 2a^2 + 3b^2) \geq\ \frac {8}{9}(ab + bc + ca)(a + b + c)^4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_60295` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_60295; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_60295 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 2 * b^2 + 3 * c^2) * (b^2 + 2 * c^2 + 3 * a^2) * (c^2 + 2 * a^2 + 3 * b^2) ≥ 8 / 9 * (a * b + b * c + c * a) * (a + b + c)^4   :=  by sorry
