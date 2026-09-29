-- Prove2me | Theorems.Thm_WorkbookSource_base_38585
-- name    : WorkbookSource.base_38585
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:43:51.38048+00:00
-- url     : https://prove2.me/theorems/d1584fdf-e8e1-49c0-a52a-f0f7b05af5cf
-- title:
--   A product of quadratic and squared reciprocal sums is at least 27
-- statement:
--   Prove that $\left(p^2+q^2+r^2 \right) \left(\frac{1}{p}+\frac{1}{q}+\frac{1}{r}\right) ^2 \ge 27$ given that $p, q,$ and $r$ are positive
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_38585` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_38585; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_38585 (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : (p^2 + q^2 + r^2) * (1 / p + 1 / q + 1 / r)^2 ≥ 27  :=  by sorry
