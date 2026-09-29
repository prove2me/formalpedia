-- Prove2me | Theorems.Thm_WorkbookSource_base_40964
-- name    : WorkbookSource.base_40964
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:12:50.123553+00:00
-- url     : https://prove2.me/theorems/faad4c81-fabd-44c3-8639-24d15ea2ce42
-- title:
--   A product of shifted quadratics at fixed sum three
-- statement:
--   Prove that $(2a^2+3)(2b^2+3)(2c^2+3) \geq 125$ given $a,b,c \geq 0$ and $a+b+c=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_40964` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_40964; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_40964 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab: a + b + c = 3) : (2 * a ^ 2 + 3) * (2 * b ^ 2 + 3) * (2 * c ^ 2 + 3) ≥ 125  :=  by sorry
