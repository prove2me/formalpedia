-- Prove2me | Theorems.Thm_lean_workbook_plus_23610
-- name    : lean_workbook_plus_23610
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d3307f68-d5da-4138-8a3b-27213f459d94
-- statement:
--   Prove that if $k^2\equiv 1\pmod{8}$, then $k$ is odd
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23610 {k : ℤ} (h : k ^ 2 ≡ 1 [ZMOD 8]) : Odd k   :=  by sorry
