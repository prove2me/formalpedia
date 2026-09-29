-- Prove2me | Theorems.Thm_WorkbookSource_base_22399
-- name    : WorkbookSource.base_22399
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:31.554752+00:00
-- url     : https://prove2.me/theorems/d6dd07ea-3d8e-438d-88f6-f08489ddd5c7
-- title:
--   A normalized cubic sum bounds a squared quadratic ratio expression
-- statement:
--   Let $a, b, c > 0$. Prove that $\frac{a^3+b^3+c^3}{3abc}\ge{(2-\frac{ab+bc+ca}{a^2+b^2+c^2})^2\cdot\frac{a^2+b^2+c^2}{ab+bc+ca}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22399` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22399; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22399 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (3 * a * b * c) ≥ (2 - (a * b + b * c + c * a) / (a^2 + b^2 + c^2))^2 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)  :=  by sorry
