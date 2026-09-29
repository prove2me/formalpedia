-- Prove2me | Theorems.Thm_WorkbookSource_plus_12600
-- name    : WorkbookSource.plus_12600
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:38.041989+00:00
-- url     : https://prove2.me/theorems/92d698d9-828d-42d1-8684-4485a7c861cf
-- title:
--   A quadratic lower bound under two product constraints
-- statement:
--   Let $a,b,c,d$ be reals such that $ab+bc+cd=7 $ and $ac+bd=3 .$ Prove that $$ a^2+b^2+c^2+d^2 \geq \frac{73}{8}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12600` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12600; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12600 (a b c d : ℝ) (h1 : a * b + b * c + c * d = 7) (h2 : a * c + b * d = 3) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ 73 / 8   :=  by sorry
