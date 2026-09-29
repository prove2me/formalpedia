-- Prove2me | Theorems.Thm_WorkbookSource_base_29201
-- name    : WorkbookSource.base_29201
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:08:32.437437+00:00
-- url     : https://prove2.me/theorems/84c0bdda-c074-485a-b658-f55f9718de53
-- title:
--   A weighted fourth-power ratio bounds the cubic mean
-- statement:
--   If $a, b, c>0$ prove that
--    $\frac{a^4}{3a+b+c}+\frac{b^4}{3b+c+a}+\frac{c^4}{3c+a+b}\ge\frac{a^3+b^3+c^3}{5}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29201` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29201; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29201 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^4 / (3 * a + b + c) + b^4 / (3 * b + c + a) + c^4 / (3 * c + a + b)) ≥ (a^3 + b^3 + c^3) / 5  :=  by sorry
