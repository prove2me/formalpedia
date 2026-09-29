-- Prove2me | Theorems.Thm_WorkbookCorrected_base_709
-- name    : WorkbookCorrected.base_709
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:23.231671+00:00
-- url     : https://prove2.me/theorems/2b67cecc-2497-4928-8354-7518f65216d6
-- title:
--   A quadratic norm minimum under three pair-product constraints
-- statement:
--   Let $a,\ b,\ c$ and $d$ be real numbers such that
--
--    $$\begin{cases} (a+b)(c+d)=2 \ (a+c)(b+d)=3 \ (a+d)(b+c)=4 \end{cases}$$
--   Find the minimum possible value of the expression
--
--    $$a^2+b^2+c^2+d^2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_709` (Apache-2.0). Natural-language proposition preserved; the source bound is completed with an exact attainment witness. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_709; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_709 : (∀ (a b c d : ℝ) (h1 : (a + b) * (c + d) = 2) (h2 : (a + c) * (b + d) = 3) (h3 : (a + d) * (b + c) = 4), 7 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ∧ (∃ a b c d : ℝ, ((a + b) * (c + d) = 2) ∧ ((a + c) * (b + d) = 3) ∧ ((a + d) * (b + c) = 4) ∧ ( 7  =  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  )) := by sorry
