-- Prove2me | Theorems.Thm_WorkbookSource_base_5683
-- name    : WorkbookSource.base_5683
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:33:21.446617+00:00
-- url     : https://prove2.me/theorems/5a154863-08f4-448b-9fd0-706ede649328
-- title:
--   A quartic polynomial is positive on the open unit interval
-- statement:
--   Prove $13a^4-26a^2+13a+1>0$ for $0<a<1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5683` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5683; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5683 (a : ℝ) (h1 : 0 < a) (h2 : a < 1) : 13*a^4 - 26*a^2 + 13*a + 1 > 0  :=  by sorry
