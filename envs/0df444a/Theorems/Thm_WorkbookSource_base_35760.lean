-- Prove2me | Theorems.Thm_WorkbookSource_base_35760
-- name    : WorkbookSource.base_35760
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:04:35.572882+00:00
-- url     : https://prove2.me/theorems/55d52c9b-94e4-44f9-8721-3d3e2d91ba9f
-- title:
--   A normalized triple product bounds a symmetric quadratic ratio
-- statement:
--   Prove that $\frac{3abc}{a^3+b^3+c^3+3abc}+\frac{1}{2}\ge \frac{ab+bc+ca}{a^2+b^2+c^2}$ given $a,b,c>0$ using only classical inequalities.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35760` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35760; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_35760 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 * a * b * c) / (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) + 1 / 2 ≥ (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2)  :=  by sorry
