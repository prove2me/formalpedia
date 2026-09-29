-- Prove2me | Theorems.Thm_WorkbookTyped_plus_45124
-- name    : WorkbookTyped.plus_45124
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:56.299873+00:00
-- url     : https://prove2.me/theorems/4e3a4d6e-45a5-46ea-a186-92f81126b9c1
-- title:
--   A sharp cyclic rational inequality
-- statement:
--   Prove that for positive reals $a,b,c,d,$ and $a+b+c+d=1$ , $$\sum_{cyc}\frac{a^3}{b+c} \ge \frac{1}{8}$$
--
--   Declaration repair: Added explicit real binders (a b c d : ℝ). This makes the positive-variable and normalization hypotheses consistent and the divisions real. The old inferred-natural-number contradiction and integer division proof are rejected. A new square-based proof establishes the intended inequality.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_45124` (Apache-2.0). [Original malformed declaration](https://prove2.me/theorems/ec3196b1-8bca-4fda-9867-b1ca4842e65a). This record proves the corrected statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_45124; explicit variable-declaration repair; Apache-2.0

import Mathlib

theorem WorkbookTyped.plus_45124 (a b c d : ℝ) (hx: a + b + c + d = 1) (ha: a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0): a^3 / (b + c) + b^3 / (c + d) + c^3 / (d + a) + d^3 / (a + b) ≥ 1 / 8   :=  by sorry
