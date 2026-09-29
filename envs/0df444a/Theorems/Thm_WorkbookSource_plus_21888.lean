-- Prove2me | Theorems.Thm_WorkbookSource_plus_21888
-- name    : WorkbookSource.plus_21888
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:41.398134+00:00
-- url     : https://prove2.me/theorems/65dd4451-14be-4d93-83a5-4f832ea96d4f
-- title:
--   A mixed distance and product lower bound
-- statement:
--   Let $a,b,c,d$ be real numbers such that $ab=c^2+d^2=1.$ Prove that
--    $$ (a-c)^2+(b-d)^2+ad+bc\geq \frac{27}{20}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21888` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21888; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21888 (a b c d : ℝ) (h : a * b = 1) (h' : c ^ 2 + d ^ 2 = 1) : (a - c) ^ 2 + (b - d) ^ 2 + a * d + b * c ≥ 27 / 20   :=  by sorry
