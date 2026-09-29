-- Prove2me | Theorems.Thm_WorkbookCorrected_base_49865
-- name    : WorkbookCorrected.base_49865
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:07.138014+00:00
-- url     : https://prove2.me/theorems/f5951744-6c35-4c52-b6c9-18963b231731
-- title:
--   A product of quadratic expressions under unit sum
-- statement:
--   Prove $54a^{2}b^{2}\leq 4(a^{2}b^{2}+a^{2}+b^{2})(a^{2}+b^{2}+1)$ , where $a,b$ are positive reals and $a+b=1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49865` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49865; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_49865 (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (h : a + b = 1) : 54 * a ^ 2 * b ^ 2 ≤ 4 * (a ^ 2 * b ^ 2 + a ^ 2 + b ^ 2) * (a ^ 2 + b ^ 2 + 1)  :=  by sorry
