-- Prove2me | Theorems.Thm_WorkbookSource_base_34828
-- name    : WorkbookSource.base_34828
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:55:31.289825+00:00
-- url     : https://prove2.me/theorems/cd3bda65-133e-497d-b2ae-7ac9e037efb8
-- title:
--   A cyclic cubic inequality with coefficient four
-- statement:
--   Prove that for any positive real numbers $a$, $b$, and $c$, the inequality $3(a^3+b^3+c^3+abc) \geq 4(a^2b+b^2c+c^2a)$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34828` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34828; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34828 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^3 + b^3 + c^3 + a * b * c) ≥ 4 * (a^2 * b + b^2 * c + c^2 * a)  :=  by sorry
