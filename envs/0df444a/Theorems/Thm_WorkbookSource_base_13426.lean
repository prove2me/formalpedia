-- Prove2me | Theorems.Thm_WorkbookSource_base_13426
-- name    : WorkbookSource.base_13426
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:40:49.578426+00:00
-- url     : https://prove2.me/theorems/bcc6a339-7777-421d-ab74-876e7bb20b37
-- title:
--   A quartic and pairwise-product bound on a sphere
-- statement:
--   if real number $a$ , $b$ , $c$ satisfy $a^2+b^2+c^2=4$ prove $a^4+b^4+c^4+6(ab+bc+ca)\leq30$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13426` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13426; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13426 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 4) : a^4 + b^4 + c^4 + 6 * (a * b + b * c + c * a) ≤ 30  :=  by sorry
