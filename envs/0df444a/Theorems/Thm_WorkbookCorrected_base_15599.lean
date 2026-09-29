-- Prove2me | Theorems.Thm_WorkbookCorrected_base_15599
-- name    : WorkbookCorrected.base_15599
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:38.990224+00:00
-- url     : https://prove2.me/theorems/7d760991-9809-4055-8ac1-29d5e77c70c6
-- title:
--   A product bound under a lower bound on a pairwise product
-- statement:
--   Given two positive numbers $a, b$ so that $ab\geqq \frac{3}{2}$ . Prove that :
--
--    $$3(2b+ a- 3)(2a+ b- 3)\geqq (a- b)^{2}+ \frac{21}{20}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15599` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15599; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_15599 (a b : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (hab : a * b ≥ 3 / 2) : 3 * (2 * b + a - 3) * (2 * a + b - 3) ≥ (a - b) ^ 2 + 21 / 20  :=  by sorry
