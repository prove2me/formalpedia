-- Prove2me | Theorems.Thm_WorkbookSource_problem_45345
-- name    : WorkbookSource.problem_45345
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:52.520202+00:00
-- url     : https://prove2.me/theorems/5ab2304a-483c-4782-aa35-8c6eedd56d9c
-- title:
--   A cubic bound on an interval
-- statement:
--   Let $u=a+b+c,v=ab+bc+ca,w=abc$ .
--   By Schur we get $w\ge \frac{4uv-u^3}{9}=\frac{4v-9}{3}$
--   While
--   $x=\sqrt{\frac{a^2+b^2+c^2}{3}}=\sqrt{\frac{9-2v}{3}}\Longleftrightarrow v=\frac{9-3x^2}{2}$
--   So we just need to prove
--   $3-2x^2\ge \frac{x}{2}\cdot ( 3x^2-16x+15)\Longleftrightarrow (x-2)(x-1)^2\le 0$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_45345; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45345; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45345 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 2) : 3 - 2 * x ^ 2 ≥ x / 2 * (3 * x ^ 2 - 16 * x + 15)  :=  by sorry
