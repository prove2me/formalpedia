-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_18160
-- name    : WorkbookCorrected.plus_18160
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:21:00.919243+00:00
-- url     : https://prove2.me/theorems/6bb324d3-bdf9-46e9-a09b-be01ba6e2a8d
-- title:
--   Bounds on a sum under a cube-root constraint
-- statement:
--   Let $a,b\ge0$ satisfy $\sqrt[3]{1+a}+\sqrt[3]{1+2b}=3$. Then
--   \[\frac{159}{2}-54\sqrt2\le a+b\le7.\]
--
--   Formalization Note: Real cube roots are expressed through their cubing equations. This repairs the natural-number division in the original fractional exponents and preserves the nonnegative domain, root-sum condition and both requested bounds.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_18160 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_18160; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_18160 : ∀ (a b u v : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : u^3=1+a) (hv : v^3=1+2*b) (h : u+v=3),
    159/2-54*Real.sqrt 2 ≤ a+b ∧ a+b ≤ 7 := by sorry
